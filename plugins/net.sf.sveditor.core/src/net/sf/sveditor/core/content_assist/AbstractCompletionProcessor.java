package net.sf.sveditor.core.content_assist;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;


public abstract class AbstractCompletionProcessor {
	protected List<SVCompletionProposal>		fCompletionProposals;
	
	protected boolean							fDebug = false;
	private static final String 				fBuiltInMacroProposals[] = { 
		"define", "include" 
	};
	
	protected abstract ISVDBIndexIterator getIndexIterator();
	
	protected abstract SVDBFile getSVDBFile();
	
	protected void addProposal(SVCompletionProposal p) {
		boolean found = false;
		for (SVCompletionProposal p_t : fCompletionProposals) {
			if (p_t.getReplacement().equals(p.getReplacement())) {
				found = true;
				break;
			}
		}
		
		if (!found) {
			fCompletionProposals.add(p);
		}
	}
	

	public void computeProposals(
			IBIDITextScanner 	scanner,
			SVDBFile			active_file,
			int					lineno) {
		
		fCompletionProposals.clear();
		
		// Prefix for the completion string
		String pre = null;
		
		// Trigger characters and string prior to the trigger (if any)
		String trigger = null, root = null;

		// Start marks the point just after the trigger character
		long start = scanner.getPos();
		scanner.setScanFwd(false);

		
		debug("computeCompletionProposals: ");

		SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				active_file, lineno);

		if (src_scope == null) {
			debug("[WARN] cannot locate source scope");
		} else {
			debug("Source scope: " + src_scope.getName());
		}

		int c = -1, last_c = -1;

		long offset = scanner.getPos();

		// Scan backwards to an activation character or the beginning of
		// line
		while ((c = scanner.get_ch()) != -1) {

			if (c == '.' || c == '`' ||	
					(c == ':' && last_c == ':')	|| c == '\n' ||
					c == ',' || c == '(') {
				break;
			} else if (c == ')') {
				// scan back to matching
				int matchLevel = 1;
				while ((c = scanner.get_ch()) != -1) {
					if (c == '(') {
						matchLevel--;
					} else if (c == ')') {
						matchLevel++;
					}
				}
			}
			last_c = c;
		}

		if (c == '.' || c == '`') {
			trigger = "" + (char) c;
		} else if (c == ':' && last_c == ':') {
			trigger = "::";
		} else {
			trigger = "";
		}

		start = scanner.getPos() + 1;

		if (trigger.equals("`")) {
			// No need to scan backwards. The stem is all we have
			pre = scanner.get_str(start, (int)(offset-start-1)).trim();

			findPreProcProposals(scanner, root, trigger, pre, (int)start);

		} else if (!trigger.equals("")) {


			// There is a trigger, so use that as a reference point
			pre = scanner.get_str(start, (int)(offset - start - 1)).trim();

			// Now, look before the trigger to see what we have
			// idx -= trigger.length();

			if (src_scope != null) {
				findTriggeredProposals(scanner, src_scope, 
						(int)(start - trigger.length()), 
						trigger,
						pre, (int)start);
			}
		} else {

			System.out.println("c=" + (char)c);

			if (c == '(' || c == ',' || c == '>' || c == '<') {
				start = scanner.getPos()+1;

				// Scan forward to avoid any whitespace
				while ((c = scanner.get_ch()) != -1 && start < offset &&  
						Character.isWhitespace(c)) {
					start++;
				}
				pre = scanner.get_str(start, (int)scanner.getPos());
			} else {
				// No recognizable trigger character, so set 'pre' based on
				// seeking backwards from the offset passed in
				// idx = offset - 1;
				scanner.seek(offset-1);
				scanner.setScanFwd(false);

				// Only works in certain cases...
				while ((c = scanner.get_ch()) != -1
						&& !Character.isWhitespace(c)) {}

				start = scanner.getPos()+1;
				pre = scanner.get_str(
						(int)start, (int)(offset-start-2)).trim();
			}

			findUntriggeredProposal(scanner, root, trigger, pre, (int)start);
		}
		
		order_proposals(pre, fCompletionProposals);
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
	 * @param pre
	 */
	private void findUntriggeredProposal(
			IBIDITextScanner			scanner,
			String 						root,
			String 						trigger,
			String 						pre,
			int 						start) {
		ISVDBIndexIterator index_iterator = getIndexIterator();
		
		debug("findUntriggeredProposal: root=" + root + " pre=" + pre);

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
					if (isPrefix(pre, p)) {
						addProposal(p, start, pre.length());
					}
				}
			}

			// TODO: Search this scope and enclosing scopes for functions,
			// tasks, and variables
			// TODO: If one of the enclosing scopes is a class scope, then
			// search the base-class tree as well
			addMatchingTasksVars(src_scope, root, trigger, pre, start);

			if (src_scope.getType() == SVDBItemType.Class) {
				addClassHierarchyItems(index_iterator, 
						(SVDBModIfcClassDecl)src_scope, root, trigger,
						pre, start);
			}

			src_scope = src_scope.getParent();
		}

		for (SVDBItem it : getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function) {
				if (it.getName() != null && (pre.equals("") 
						|| isPrefix(pre, it))) {
					addProposal(it, start, pre.length());
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
					(pre.equals("") || isPrefix(pre, it))) {
				addProposal(it, start, pre.length());
			}
		}
	}

	/**
	 * Find proposals that result from a triggered content-assist request
	 * 
	 * Typical strings will be something like: a.b<request>
	 * 
	 * @param viewer
	 * @param src_scope
	 * @param pre_trigger_idx
	 * @param trigger
	 * @param pre
	 * @param start
	 * @param proposals
	 */
	private void findTriggeredProposals(
			IBIDITextScanner	scanner,
			SVDBScopeItem		src_scope,
			int					pre_trigger_idx,
			String				trigger,
			String				pre,
			int					start) {
		ISVDBIndexIterator index_iterator = getIndexIterator();
		
		debug("findTriggeredProposals: " + src_scope.getName() + 
				" pre=" + pre + " trigger=" + trigger);
		
		/*
		try {
		debug("    char @ pre-trigger index: " + 
				viewer.getDocument().getChar(pre_trigger_idx));
		} catch (Exception e) { }
		 */

		// TODO: not sure
		scanner.seek(pre_trigger_idx);
		
		String preTrigger = 
			SVExpressionUtils.extractPreTriggerPortion(scanner);
		
		debug("    preTrigger=" + preTrigger);
		List<SVDBItem> info = SVExpressionUtils.processPreTriggerPortion(
				index_iterator, src_scope, preTrigger, true);
		
		final List<SVDBItem> result_f = new ArrayList<SVDBItem>();
		
		if (info != null && info.size() > 0) {
			// Get the last item
			SVDBItem res = info.get(info.size()-1);
			final String pre_f = pre;
			
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
			addProposal(it, start, pre.length());
		}
	}

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
	 */
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

	/**
	 * findPreProcProposals()
	 * 
	 * Find macro completion proposals
	 * 
	 * @param proposals
	 * @param pre
	 */
	private void findPreProcProposals(
			IBIDITextScanner			scanner,
			String 						root, 
			String 						trigger, 
			String 						pre,
			int 						start) {
		ISVDBIndexIterator index_it = getIndexIterator();

		if (pre.startsWith("include")) {
			boolean leading_quote = false, trailing_quote = false;
			String display = "", replacement = "";

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
					display = file.getName();
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
					/*
							SVUiPlugin.getImage(ISVIcons.INCLUDE_OBJ),
							display, null, null), proposals_f);
					 */
				}
			}
		} else {
			for (String p : fBuiltInMacroProposals) {
				if (p.toLowerCase().startsWith(pre.toLowerCase())) {
					addProposal(new SVCompletionProposal(p, start, pre.length()));
				}
			}
			// TODO: Collect matching macro names from the build path
			/*
			for (SVDBFile f : index.getPreProcFileMap().values()) {
				addMacroProposals(pre, f, doc, start, proposals);
			}
			 */
			
			ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
			
			while (item_it.hasNext()) {
				SVDBItem it = item_it.nextItem();
				
				if (isPrefix(pre, it)) {
					addProposal(it, start, pre.length());
				}
				System.out.println("it=" + it.getName());
			}
			System.out.println("[TODO] Collect matching macro names from build path");
		}
	}


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
		for (int i = 0; i < proposals.size(); i++) {
			SVCompletionProposal p_i = proposals.get(i);
			for (int j = i + 1; j < proposals.size(); j++) {
				SVCompletionProposal p_j = proposals.get(j);

				if (p_i.getItem().getName().compareTo(p_j.getItem().getName()) > 0) {
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
				
				if (prefix.compareTo(p_i.getItem().getName()) >
						prefix.compareTo(p_j.getItem().getName())) {
					proposals.set(i, p_j);
					proposals.set(j, p_i);
					p_i = p_j;
				}
			}
		}
	}

	protected void addProposal(
			SVDBItem 		it, 
			int 			replacementOffset, 
			int 			replacementLength) {
		
		switch (it.getType()) {
			case Function:
			case Task: 
				addTaskFuncProposal(
						it, replacementOffset, replacementLength);
				break;
				
			case Macro:
				addMacroProposal(
						it, replacementOffset, replacementLength);
				break;
				
			case Class:
				addClassProposal(
						it, replacementOffset, replacementLength);
				break;
				
			default:
				/** TODO: 
				p = new CompletionProposal(it.getName(),
						replacementOffset, replacementLength, 
						it.getName().length(), SVDBIconUtils.getIcon(it),
						null, null, null);
				 */
				break;
		}
		
		/** TODO: 
		if (p != null) {
			addProposal(p, proposals);
		}
		 */
	}

	private static void addTaskFuncProposal(
			SVDBItem 					it,
			int							replacementOffset,
			int							replacementLength) {
		/** TODO:  
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		 */
		
		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBTaskFuncScope tf = (SVDBTaskFuncScope)it;
		
		d.append(it.getName() + "(");
		r.append(it.getName() + "(");
		
		for (int i=0; i<tf.getParams().size(); i++) {
			SVDBTaskFuncParam param = tf.getParams().get(i);
			
			d.append(param.getTypeName() + " " + param.getName());
			r.append("${");
			r.append(param.getName());
			r.append("}");
			
			if (i+1 < tf.getParams().size()) {
				d.append(", ");
				r.append(", ");
			}
		}
		d.append(")");
		r.append(")");
		
		if (it.getType() == SVDBItemType.Function &&
				!it.getName().equals("new")) {
			d.append(" : ");
			d.append(tf.getReturnType());
		}
		
		// Find the class that this function belongs to (if any)
		SVDBItem class_it = it;
		
		while (class_it != null && class_it.getType() != SVDBItemType.Class) {
			class_it = class_it.getParent();
		}

		/** TODO: 
		Template t = new Template(d.toString(), 
				(class_it != null)?class_it.getName():"", "CONTEXT",
				r.toString(), (tf.getParams().size() == 0));
		
		p = new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));

		boolean found = false;
		for (ICompletionProposal p_t : proposals) {
			if (p_t.getDisplayString().equals(p.getDisplayString())) {
				found = true;
			}
		}
		if (!found) {
			proposals.add(p);
		}
		 */
	}
	
	private static void addMacroProposal(
			SVDBItem 					it,
			int							replacementOffset,
			int							replacementLength) {
		/** TODO: 
		ICompletionProposal			p;

		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		 */

		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBMacroDef md = (SVDBMacroDef)it;
		
		d.append(it.getName() + "(");
		r.append(it.getName() + "(");
		
		for (int i=0; i<md.getParameters().size(); i++) {
			String param = md.getParameters().get(i);
			
			d.append(param);
			r.append("${");
			r.append(param);
			r.append("}");
			
			if (i+1 < md.getParameters().size()) {
				d.append(", ");
				r.append(", ");
			}
		}
		d.append(")");
		r.append(")");
		
		/** TODO: 
		Template t = new Template(d.toString(), "", "CONTEXT",
				r.toString(), true);
		
		p = new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
		proposals.add(p);
		 */
	}

	private static void addClassProposal(
			SVDBItem 					it,
			int							replacementOffset,
			int							replacementLength) {
		
		/** TODO: 
		ICompletionProposal			p;

		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		 */

		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBModIfcClassDecl cl = (SVDBModIfcClassDecl)it;
		
		r.append(it.getName());
		d.append(it.getName());
		
		if (cl.getParameters().size() > 0) {
			r.append(" #(");
			for (int i=0; i<cl.getParameters().size(); i++) {
				SVDBModIfcClassParam pm = cl.getParameters().get(i);

				r.append("${");
				r.append(pm.getName());
				r.append("}");
				
				if (i+1 < cl.getParameters().size()) {
					r.append(", ");
				}
			}
			r.append(")");
		}

		/** TODO: 
		Template t = new Template(
				d.toString(), "", "CONTEXT", r.toString(), true);
		
		p = new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
		
		proposals.add(p);
		 */
	}

	
	
	protected void debug(String msg) {
		if (fDebug) {
			System.out.println(msg);
		}
	}

}
