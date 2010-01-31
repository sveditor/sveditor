package net.sf.sveditor.core.content_assist;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBContentAssistIncludeNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindContentAssistNameMatcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;


public abstract class AbstractCompletionProcessor {
	protected List<SVCompletionProposal>		fCompletionProposals;
	
	protected LogHandle							fLog;
	/**
	private static final String 				fBuiltInMacroProposals[] = { 
		"define", "include" 
	};
	 */
	
	public AbstractCompletionProcessor() {
		fCompletionProposals = new ArrayList<SVCompletionProposal>();
	}
	
	protected abstract ISVDBIndexIterator getIndexIterator();
	
	protected abstract SVDBFile getSVDBFile();
	
	protected void addProposal(SVCompletionProposal p) {
		boolean found = false;
		
		for (SVCompletionProposal p_t : fCompletionProposals) {
			if (p_t.equals(p)) {
				found = true;
				break;
			}
		}
		
		if (!found) {
			fCompletionProposals.add(p);
		}
	}
	
	public List<SVCompletionProposal> getCompletionProposals() {
		return fCompletionProposals;
	}

	public void computeProposals(
			IBIDITextScanner 	scanner,
			SVDBFile			active_file,
			int					lineno) {
		SVExpressionUtils expr_utils = new SVExpressionUtils(
				new SVDBFindContentAssistNameMatcher());
		
		fCompletionProposals.clear();
		
		// Trigger characters and string prior to the trigger (if any)

		debug("computeCompletionProposals: ");

		SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				active_file, lineno);

		if (src_scope == null) {
			debug("[WARN] cannot locate source scope");
		} else {
			debug("Source scope: " + src_scope.getName());
		}

		SVExprContext ctxt = expr_utils.extractExprContext(scanner, false);
		debug("ctxt: trigger=" + ctxt.fTrigger + " root=" + ctxt.fRoot + 
				" leaf=" + ctxt.fLeaf + " start=" + ctxt.fStart);
		
		/*
		if (ctxt.fTrigger == null) {
			findUntriggeredProposal(scanner, ctxt.fRoot, ctxt.fTrigger, 
					ctxt.fLeaf, ctxt.fStart);
		} else if (ctxt.fTrigger.equals("`")) {
			// No need to scan backwards. The stem is all we have
			findPreProcProposals(scanner, ctxt.fRoot, ctxt.fTrigger, ctxt.fLeaf, ctxt.fStart);
		} else {
			// Now, look before the trigger to see what we have

			if (src_scope != null) {
				findTriggeredProposals(scanner, src_scope,
						ctxt.fRoot, ctxt.fTrigger, ctxt.fLeaf, ctxt.fStart);
			} else {
				System.out.println("[WARN] src_scope is null");
			}
		}
		*/
		// If this is an include lookup, then use a different matching strategy
		if (ctxt.fTrigger != null && ctxt.fRoot != null &&
				ctxt.fTrigger.equals("`") && ctxt.fRoot.equals("include")) {
			expr_utils.setMatcher(new SVDBContentAssistIncludeNameMatcher());
		}
		
		List<SVDBItem> items = expr_utils.findItems(
				getIndexIterator(), src_scope, ctxt, true);
		
		if (ctxt.fTrigger != null && ctxt.fTrigger.equals("`") &&
				ctxt.fRoot.startsWith("include")) {
			String replacement = "";

			for (SVDBItem it : items) {
				File file = new File(it.getName());
				replacement = file.getName();
				
				// Add quotes in if not present already...
				if (!scanner.get_str(ctxt.fStart-1, 1).equals("\"")) {
					replacement = "\"" + replacement;
				}
				replacement += "\"";
				
				addProposal(new SVCompletionProposal(
						replacement, ctxt.fStart, ctxt.fLeaf.length()));
			}
		} else {
			for (SVDBItem it : items) {
				addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
		}
		
		order_proposals(ctxt.fLeaf, fCompletionProposals);
	}
	
	/**
	 * findUntriggeredProposal
	 * 
	 * Find a proposal based on a request for content assist that did not start
	 * with a trigger string ( . ` ::)
	 * 
	 * These proposals are made based on the prefix string and elements from the
	 * index
	 * 
	 * @param proposals
	 * @param leaf
	private void findUntriggeredProposal(
			IBIDITextScanner			scanner,
			String 						root,
			String 						trigger,
			String 						leaf,
			int 						start) {
		ISVDBIndexIterator index_iterator = getIndexIterator();
		
		debug("findUntriggeredProposal: root=" + root + " leaf=" + leaf);

		scanner.seek(start);
		int lineno = scanner.getLocation().getLineNo();

		SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				getSVDBFile(), lineno);
		
		if (src_scope == null) {
			System.out.println("[WARN] cannot locate source scope");
		}

		// Figure out which scope we're in and collect info from there...

		// Begin working outwards
		while (src_scope != null) {
			
			if (src_scope.getType() == SVDBItemType.Task || 
					src_scope.getType() == SVDBItemType.Function) {
				SVDBTaskFuncScope tf = (SVDBTaskFuncScope)src_scope;
				
				for (SVDBTaskFuncParam p : tf.getParams()) {
					if (isPrefix(leaf, p)) {
						addProposal(p, start, leaf.length());
					}
				}
			}

			// TODO: Search this scope and enclosing scopes for functions,
			// tasks, and variables
			// TODO: If one of the enclosing scopes is a class scope, then
			// search the base-class tree as well
			addMatchingTasksVars(src_scope, root, trigger, leaf, start);

			if (src_scope.getType() == SVDBItemType.Class) {
				addClassHierarchyItems(index_iterator, 
						(SVDBModIfcClassDecl)src_scope, root, trigger,
						leaf, start);
			}

			src_scope = src_scope.getParent();
		}

		for (SVDBItem it : getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function) {
				if (it.getName() != null && (leaf.equals("") 
						|| isPrefix(leaf, it))) {
					addProposal(it, start, leaf.length());
				}
			} else if (it.getType() == SVDBItemType.Module
					|| it.getType() == SVDBItemType.Class) {
				// TODO: recurse and search the scope for this
			}
		}

		// Collect all matching class names from the build path
		ISVDBItemIterator<SVDBItem> item_it = index_iterator.getItemIterator();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			if (it.getName() != null && 
					(it.getType() != SVDBItemType.File) &&
					(it.getType() != SVDBItemType.Macro) &&
					(it.getType() != SVDBItemType.Include) &&
					(leaf.equals("") || isPrefix(leaf, it))) {
				addProposal(it, start, leaf.length());
			}
		}
	}
	 */

	/**
	 * Find proposals that result from a triggered content-assist request
	 * 
	 * Typical strings will be something like: a.b<request>
	 * 
	 * @param viewer
	 * @param src_scope
	 * @param pre_trigger_idx
	 * @param trigger
	 * @param leaf
	 * @param start
	 * @param proposals
	private void findTriggeredProposals(
			IBIDITextScanner	scanner,
			SVDBScopeItem		src_scope,
			String				root,
			String				trigger,
			String				leaf,
			int					start) {
		ISVDBIndexIterator index_iterator = getIndexIterator();
		SVExpressionUtils expr_utils = new SVExpressionUtils();
		
		debug("findTriggeredProposals: " + src_scope.getName() + 
				" pre=" + leaf + " trigger=" + trigger);
		
		debug("    preTrigger=" + leaf);
		List<SVDBItem> info = expr_utils.processPreTriggerPortion(
				index_iterator, src_scope, root, true);
		
		final List<SVDBItem> result_f = new ArrayList<SVDBItem>();
		
		if (info != null && info.size() > 0) {
			// Get the last item
			SVDBItem res = info.get(info.size()-1);
			final String pre_f = leaf;
			
			debug("use " + res.getName());
			
			SVDBModIfcClassDecl res_c = (SVDBModIfcClassDecl)res;
			SVDBFindSuperClass finder_sc = new SVDBFindSuperClass(index_iterator);

			while (res_c != null) {
				
				for (SVDBItem it : res_c.getItems()) {
					if (isPrefix(pre_f, it)) {
						result_f.add(it);
					}
				}

				if (res_c.getSuperClass() != null) {
					res_c = finder_sc.find(res_c);
				} else {
					res_c = null;
				}
			}
		}
		
		for (SVDBItem it : result_f) {
			addProposal(it, start, leaf.length());
		}
	}
	 */

	/**
	private void addMatchingTasksVars(
			SVDBScopeItem 	src_scope, 
			String 			root, 
			String 			trigger, 
			String 			pre, 
			int 			start) {
		debug("addMatchingTasksVars: " + src_scope.getName() + " pre=" + pre);

		for (SVDBItem it : src_scope.getItems()) {
			debug("    it=" + it.getName() + " type=" +	it.getType());
			if (it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function
					|| it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.TaskFuncParam) {
				if (isPrefix(pre, it)) {
					addProposal(it, start, pre.length());
				}
			}
		}
	}
	 */
	
	/**
	private void addMacroProposals(
			String							pre,
			SVDBScopeItem					scope,
			int								replacementOffset) {
		
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Macro) {
				if (it.getName() != null && 
						(pre.equals("") || isPrefix(pre, it))) {
					addProposal(it, replacementOffset, pre.length());
				}
			} else if (it instanceof SVDBScopeItem) {
				addMacroProposals(
						pre, (SVDBScopeItem)it, replacementOffset);
			}
		}
	}
	 */


	/**
	 * Traverse the class hierarchy and add tasks, functions, and members to the
	 * completion proposals
	 * 
	 * @param searcher
	 * @param src_scope
	 * @param doc
	 * @param root
	 * @param trigger
	 * @param pre
	 * @param start
	 * @param proposals
	private void addClassHierarchyItems(
			ISVDBIndexIterator			index_it,
			SVDBModIfcClassDecl 		src_scope, 
			String 						root,
			String 						trigger, 
			String 						pre, 
			int 						start) {
		debug("addClassHierarchyItems()");

		while (true) {
			debug("src_scope=" + src_scope.getName()
					+ " superClass=" + src_scope.getSuperClass());
			SVDBModIfcClassDecl src_scope_t = src_scope;
			SVDBFindNamedModIfcClassIfc finder_class =
				new SVDBFindNamedModIfcClassIfc(index_it);
			
			if (src_scope.getSuperClass() == null
					|| (src_scope = finder_class.find(
							src_scope.getSuperClass())) == null) {
				debug("End expansion: " + src_scope_t.getName());
				debug("    SuperClass="	+ src_scope_t.getSuperClass());
				debug("    Find="
						+ finder_class.find(src_scope_t.getSuperClass()));
				break;
			}

			addMatchingTasksVars(src_scope, root, trigger, pre, start);
		}
	}
	 */

	/**
	 * findPreProcProposals()
	 * 
	 * Find macro completion proposals
	 * 
	 * @param proposals
	 * @param pre
	private void findPreProcProposals(
			IBIDITextScanner			scanner,
			String 						root, 
			String 						trigger, 
			String 						pre,
			int 						start) {
		ISVDBIndexIterator index_it = getIndexIterator();

		if (pre.startsWith("include")) {
			boolean leading_quote = false, trailing_quote = false;
			String replacement = "";

			// Look at the point beyond the '`include'
			String post_include = pre.substring("include".length());

			start += "include".length();

			// Now, account for any whitespace
			while (post_include.length() > 0
					&& Character.isWhitespace(post_include.charAt(0))) {
				post_include = post_include.substring(1);
				start++;
			}

			if (post_include.startsWith("\"")) {
				// strip away the quote
				leading_quote = true;
				post_include = post_include.substring(1);
				start++;
			}

			// look for include files that match the user-specified pattern
			
			// Collect all matching class names from the build path
			ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
			
			while (item_it.hasNext()) {
				SVDBItem it = item_it.nextItem();
				
				if (it.getType() != SVDBItemType.Include) {
					continue;
				}
				
				File file = new File(it.getName());
				
				if (file.getName().toLowerCase().startsWith(post_include.toLowerCase())) {
					replacement = file.getName();

					// Add quotes in if not present already...
					if (!leading_quote) {
						replacement = "\"" + replacement;
					}
					if (!trailing_quote) {
						replacement += "\"";
					}

					int replacement_length = post_include.length();
					// replacementString
					// replacementOffset
					// replacementLength
					// cursorPosition
					addProposal(new SVCompletionProposal(replacement,
							start, replacement_length));
				}
			}
		} else {
			for (String p : fBuiltInMacroProposals) {
				if (p.toLowerCase().startsWith(pre.toLowerCase())) {
					addProposal(new SVCompletionProposal(p, start, pre.length()));
				}
			}
			ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
			
			while (item_it.hasNext()) {
				SVDBItem it = item_it.nextItem();
				
				if (it.getType() == SVDBItemType.Macro &&
						isPrefix(pre, it)) {
					addProposal(it, start, pre.length());
				}
				debug("it=" + it.getName());
			}
		}
	}
	 */


	protected boolean isPrefix(String pre, SVDBItem it) {
		return it.getName().toLowerCase().startsWith(pre.toLowerCase());
	}

	/**
	 * order_proposals()
	 * 
	 * Re-order the proposals to be in alphabetical order
	 * 
	 * @param proposals
	 */
	private void order_proposals(String prefix, List<SVCompletionProposal> proposals) {
		
		// First eliminate any class typedefs for which the actual class is available
		for (int i=0; i<proposals.size(); i++) {
			SVCompletionProposal p = proposals.get(i);
			if (p.getItem() != null && p.getItem().getType() == SVDBItemType.Typedef) {
				boolean found = false;
				
				for (SVCompletionProposal p_t : proposals) {
					if (p_t != p && p_t.getItem() != null && 
							p_t.getItem().getName().equals(p.getItem().getName())) {
						found = true;
						break;
					}
				}
				
				if (found) {
					proposals.remove(i);
					i--;
				}
			}
		}
		for (int i = 0; i < proposals.size(); i++) {
			SVCompletionProposal p_i = proposals.get(i);
			for (int j = i + 1; j < proposals.size(); j++) {
				SVCompletionProposal p_j = proposals.get(j);
				String s_i, s_j;
				
				if (p_i.getItem() != null) {
					s_i = p_i.getItem().getName();
				} else {
					s_i = p_i.getReplacement();
				}
				
				if (p_j.getItem() != null) {
					s_j = p_j.getItem().getName();
				} else {
					s_j = p_j.getReplacement();
				}

				if (s_i.compareTo(s_j) > 0) {
					proposals.set(i, p_j);
					proposals.set(j, p_i);
					p_i = p_j;
				}
			}
		}
		
		for (int i=0; i<proposals.size(); i++) {
			SVCompletionProposal p_i = proposals.get(i);
			for (int j=i+1; j<proposals.size(); j++) {
				SVCompletionProposal p_j = proposals.get(j);

				String s_i, s_j;
				
				if (p_i.getItem() != null) {
					s_i = p_i.getItem().getName();
				} else {
					s_i = p_i.getReplacement();
				}
				
				if (p_j.getItem() != null) {
					s_j = p_j.getItem().getName();
				} else {
					s_j = p_j.getReplacement();
				}

				if (prefix.compareTo(s_i) < prefix.compareTo(s_j)) {
					proposals.set(i, p_j);
					proposals.set(j, p_i);
					p_i = p_j;
				}
			}
		}
	}

	protected void addProposal(
			SVDBItem 		it,
			String			prefix,
			int 			replacementOffset, 
			int 			replacementLength) {
		boolean found = false;
		
		for (SVCompletionProposal p : fCompletionProposals) {
			if (p.getItem() != null && p.getItem().equals(it)) {
				found = true;
				break;
			}
		}
		
		if (!found) {
			debug("addProposal: " + it.getName());
			addProposal(new SVCompletionProposal(it, prefix, 
					replacementOffset, replacementLength));
		}
	}
	
	protected void debug(String msg) {
		fLog.debug(msg);
	}

}
