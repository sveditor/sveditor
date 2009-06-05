package net.sf.sveditor.ui.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

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
import net.sf.sveditor.ui.ISVIcons;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.jface.text.templates.DocumentTemplateContext;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateContextType;
import org.eclipse.jface.text.templates.TemplateProposal;

public class SVCompletionProcessor implements IContentAssistProcessor {

	private SVEditor 	fEditor;
	private boolean		fDebugEn = true;

	private static final char[] PROPOSAL_ACTIVATION_CHARS = { '.', ':' };
	private static final String fBuiltInMacroProposals[] = { "define",
			"include" };

	private final IContextInformation NO_CONTEXTS[] = new IContextInformation[0];

	public void init(SVEditor editor) {
		fEditor = editor;
	}

	public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer,
			int offset) {
		List<ICompletionProposal> proposals = new ArrayList<ICompletionProposal>();
		
		// Prefix for the completion string
		String pre = null;
		
		// Trigger characters and string prior to the trigger (if any)
		String trigger = null, root = null;

		// Start marks the point just after the trigger character
		int start = offset;

		IDocument doc = viewer.getDocument();

		
		debug("computeCompletionProposals: ");

		try {
			int lineno = 0;

			lineno = doc.getLineOfOffset(start);

			SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
					fEditor.getSVDBFile(), lineno);
			
			if (src_scope == null) {
				debug("[WARN] cannot locate source scope");
			} else {
				debug("Source scope: " + src_scope.getName());
			}

			int c = -1, last_c = -1, idx = offset - 1;

			// Scan backwards to an activation character or the beginning of
			// line
			while (idx >= 0) {
				c = doc.getChar(idx);

				if (c == '.' || c == '`' ||	
						(c == ':' && last_c == ':')	|| c == '\n' ||
						c == ',' || c == '(') {
					break;
				} else if (c == ')') {
					// scan back to matching
					int matchLevel = 1;
					while (idx >= 0) {
						if (c == '(') {
							matchLevel--;
						} else if (c == ')') {
							matchLevel++;
						}
					}
				}
				last_c = c;
				idx--;
			}

			if (c == '.' || c == '`') {
				trigger = "" + (char) c;
			} else if (c == ':' && last_c == ':') {
				trigger = "::";
			} else {
				trigger = "";
			}

			start = idx + 1;

			if (trigger.equals("`")) {
				// No need to scan backwards. The stem is all we have
				pre = doc.get(idx + 1, offset - idx - 1).trim();

				findPreProcProposals(doc, root, trigger, pre, start, proposals);
				
			} else if (!trigger.equals("")) {
				

				// There is a trigger, so use that as a reference point
				pre = doc.get(idx + 1, offset - idx - 1).trim();

				start = idx + 1;

				// Now, look before the trigger to see what we have
				idx -= trigger.length();

				if (src_scope != null) {
					findTriggeredProposals(viewer, src_scope, idx, trigger,
							pre, start, proposals);
				}
			} else {
				
				System.out.println("c=" + (char)c);
				
				if (c == '(' || c == ',' || c == '>' || c == '<') {
					start = idx+1;
					
					// Scan forward to avoid any whitespace
					while (start < doc.getLength() && start < offset &&  
							Character.isWhitespace(doc.getChar(start))) {
						idx++;
						start++;
					}
					pre = doc.get(start, offset-idx-1);
				} else {
					// No recognizable trigger character, so set 'pre' based on
					// seeking backwards from the offset passed in
					idx = offset - 1;

					// Only works in certain cases...
					while (idx >= 0	&& !Character.isWhitespace(doc.getChar(idx))) {
						idx--;
					}

					start = idx + 1;
					pre = doc.get(idx + 1, offset - idx - 1).trim();
				}
				
				findUntriggeredProposal(viewer.getDocument(), root, trigger,
						pre, start, proposals);
			}

		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		order_proposals(pre, proposals);
		return proposals.toArray(new ICompletionProposal[proposals.size()]);
	}

	/**
	 * order_proposals()
	 * 
	 * Re-order the proposals to be in alphabetical order
	 * 
	 * @param proposals
	 */
	private void order_proposals(String prefix, List<ICompletionProposal> proposals) {
		for (int i = 0; i < proposals.size(); i++) {
			ICompletionProposal p_i = proposals.get(i);
			for (int j = i + 1; j < proposals.size(); j++) {
				ICompletionProposal p_j = proposals.get(j);

				if (p_i.getDisplayString().compareTo(p_j.getDisplayString()) > 0) {
					proposals.set(i, p_j);
					proposals.set(j, p_i);
					p_i = p_j;
				}
			}
		}
		
		for (int i=0; i<proposals.size(); i++) {
			ICompletionProposal p_i = proposals.get(i);
			for (int j=i+1; j<proposals.size(); j++) {
				ICompletionProposal p_j = proposals.get(j);
				
				if (prefix.compareTo(p_i.getDisplayString()) >
						prefix.compareTo(p_j.getDisplayString())) {
					proposals.set(i, p_j);
					proposals.set(j, p_i);
					p_i = p_j;
				}
			}
		}
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
			IDocument 					doc, 
			String 						root,
			String 						trigger,
			String 						pre,
			int 						start,
			List<ICompletionProposal> 	proposals) {
		ISVDBIndexIterator index_iterator = fEditor.getIndexIterator();
		
		debug("findUntriggeredProposal: root=" + root + " pre=" + pre);

		int lineno = 0;

		try {
			lineno = doc.getLineOfOffset(start);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				fEditor.getSVDBFile(), lineno);
		
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
						addProposal(p, doc, start, pre.length(), proposals);
					}
				}
			}

			// TODO: Search this scope and enclosing scopes for functions,
			// tasks, and variables
			// TODO: If one of the enclosing scopes is a class scope, then
			// search the base-class tree as well
			addMatchingTasksVars(
					src_scope, doc, root, trigger, pre, start, proposals);

			if (src_scope.getType() == SVDBItemType.Class) {
				addClassHierarchyItems(index_iterator,
						(SVDBModIfcClassDecl) src_scope, doc, root, trigger,
						pre, start, proposals);
			}

			src_scope = src_scope.getParent();
		}

		for (SVDBItem it : fEditor.getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function) {
				if (it.getName() != null && (pre.equals("") 
						|| isPrefix(pre, it))) {
					addProposal(it, doc, start, pre.length(), proposals);
				}
			} else if (it.getType() == SVDBItemType.Module
					|| it.getType() == SVDBItemType.Class) {
				// TODO: recurse and search the scope for this
			}
		}

		final String 					pre_f = pre;
		final IDocument 				doc_f = doc;
		final int						start_f = start;
		final List<ICompletionProposal> proposals_f = proposals;
		
		// Collect all matching class names from the build path
		ISVDBItemIterator<SVDBItem> item_it = index_iterator.getItemIterator();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			if (it.getName() != null && 
					(it.getType() != SVDBItemType.File) &&
					(pre_f.equals("") || isPrefix(pre_f, it))) {
				addProposal(it, doc_f, start_f, pre_f.length(), proposals_f);
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
			ITextViewer			viewer,
			SVDBScopeItem		src_scope,
			int					pre_trigger_idx,
			String				trigger,
			String				pre,
			int					start,
			List<ICompletionProposal> proposals) {
		ISVDBIndexIterator index_iterator = fEditor.getIndexIterator();
		
		debug("findTriggeredProposals: " + src_scope.getName() + 
				" pre=" + pre + " trigger=" + trigger);
		
		try {
		debug("    char @ pre-trigger index: " + 
				viewer.getDocument().getChar(pre_trigger_idx));
		} catch (Exception e) { }
		
		String preTrigger = SVExpressionUtils.extractPreTriggerPortion(
				viewer.getDocument(), pre_trigger_idx, false);
		
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
			addProposal(it, viewer.getDocument(), start, pre.length(), proposals);
		}
	}

	private void addMatchingTasksVars(SVDBScopeItem src_scope, IDocument doc,
			String root, String trigger, String pre, int start,
			List<ICompletionProposal> proposals) {
		debug("addMatchingTasksVars: " + src_scope.getName() + " pre=" + pre);

		for (SVDBItem it : src_scope.getItems()) {
			debug("    it=" + it.getName() + " type=" +	it.getType());
			if (it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function
					|| it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.TaskFuncParam) {
				if (isPrefix(pre, it)) {
					addProposal(it, doc, start, pre.length(), proposals);
				}
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
			IDocument 					doc, 
			String 						root,
			String 						trigger, 
			String 						pre, 
			int 						start,
			List<ICompletionProposal> 	proposals) {
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

			addMatchingTasksVars(src_scope, doc, root, trigger, pre, start,
					proposals);
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
			IDocument					doc,
			String 						root, 
			String 						trigger, 
			String 						pre,
			int 						start, 
			List<ICompletionProposal>	proposals) {
		ISVDBIndexIterator index_it = fEditor.getIndexIterator();

		if (pre.startsWith("include")) {
			boolean leading_quote = false, trailing_quote = false;
			String display, replacement = "";

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
			final String 					pre_f = pre;
			final IDocument 				doc_f = doc;
			final int						start_f = start;
			final List<ICompletionProposal> proposals_f = proposals;
			final boolean leading_quote_f = leading_quote;
			final boolean trailing_quote_f = trailing_quote;
			final String post_include_f = post_include;
			
			// Collect all matching class names from the build path
			ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
			
			while (item_it.hasNext()) {
				SVDBItem it = item_it.nextItem();
				
				if (it.getType() != SVDBItemType.Include) {
					continue;
				}
				
				File file = new File(it.getName());
				
				if (file.getName().toLowerCase().startsWith(post_include_f.toLowerCase())) {
					display = file.getName();
					replacement = file.getName();

					// Add quotes in if not present already...
					if (!leading_quote_f) {
						replacement = "\"" + replacement;
					}
					if (!trailing_quote_f) {
						replacement += "\"";
					}

					int replacement_length = post_include_f.length();
					// replacementString
					// replacementOffset
					// replacementLength
					// cursorPosition
					addProposal(new CompletionProposal(replacement,
							start_f, replacement_length,
							replacement.length(), 
							SVUiPlugin.getImage(ISVIcons.INCLUDE_OBJ),
							display, null, null), proposals_f);
				}
			}
		} else {
			for (String p : fBuiltInMacroProposals) {
				if (p.toLowerCase().startsWith(pre.toLowerCase())) {
					addProposal(new CompletionProposal(p, start, pre
							.length(), p.length()), proposals);
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
					addProposal(it, doc, start, pre.length(), proposals);
				}
				System.out.println("it=" + it.getName());
			}
			System.out.println("[TODO] Collect matching macro names from build path");
		}
	}
	
	private void addMacroProposals(
			String							pre,
			SVDBScopeItem					scope,
			IDocument						doc,
			int								replacementOffset,
			List<ICompletionProposal>		proposals) {
		
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Macro) {
				if (it.getName() != null && 
						(pre.equals("") || isPrefix(pre, it))) {
					addProposal(it, doc, replacementOffset, pre.length(), proposals);
				}
			} else if (it instanceof SVDBScopeItem) {
				addMacroProposals(
						pre, (SVDBScopeItem)it, doc, replacementOffset, proposals);
			}
		}
	}
	
	private static void addProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength,
			List<ICompletionProposal> 	proposals) {
		ICompletionProposal p = null;
		
		switch (it.getType()) {
			case Function:
			case Task: 
				addTaskFuncProposal(it, doc, replacementOffset, 
						replacementLength, proposals);
				break;
				
			case Macro:
				addMacroProposal(it, doc, replacementOffset,
						replacementLength, proposals);
				break;
				
			case Class:
				addClassProposal(it, doc, replacementOffset,
						replacementLength, proposals);
				break;
				
			default:
				p = new CompletionProposal(it.getName(),
						replacementOffset, replacementLength, 
						it.getName().length(), SVDBIconUtils.getIcon(it),
						null, null, null);
				break;
		}
		
		if (p != null) {
			addProposal(p, proposals);
		}
	}
	
	private static void addTaskFuncProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength,
			List<ICompletionProposal> 	proposals) {
		ICompletionProposal			p;

		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		

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
	}

	private static void addMacroProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength,
			List<ICompletionProposal> 	proposals) {
		ICompletionProposal			p;

		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		

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
		
		Template t = new Template(d.toString(), "", "CONTEXT",
				r.toString(), true);
		
		p = new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
		proposals.add(p);
	}

	private static void addClassProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength,
			List<ICompletionProposal> 	proposals) {
		ICompletionProposal			p;

		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		

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
		
		Template t = new Template(
				d.toString(), "", "CONTEXT", r.toString(), true);
		
		p = new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
		
		proposals.add(p);
	}


	/**
	 * Add a proposal to the proposals list, ensure that this proposal isn't a
	 * duplicate
	 * 
	 * @param p
	 * @param proposals
	 */
	private static void addProposal(ICompletionProposal p,
			List<ICompletionProposal> proposals) {
		boolean found = false;

		for (ICompletionProposal p_t : proposals) {
			if (p.getDisplayString().equals(p_t.getDisplayString())) {
				found = true;
				break;
			}
		}

		if (!found) {
			proposals.add(p);
		}
	}
	
	private boolean isPrefix(String pre, SVDBItem it) {
		return it.getName().toLowerCase().startsWith(pre.toLowerCase());
	}

	public IContextInformation[] computeContextInformation(
			ITextViewer viewer, int offset) {
		
		return NO_CONTEXTS;
	}

	public char[] getCompletionProposalAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	public char[] getContextInformationAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	public IContextInformationValidator getContextInformationValidator() {
		System.out.println("getContextInformationValidator()");
		// TODO Auto-generated method stub
		return null;
	}

	public String getErrorMessage() {
		// TODO Auto-generated method stub
		return null;
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}

}
