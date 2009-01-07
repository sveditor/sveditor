package net.sf.sveditor.ui.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.utils.SVDBIndexSearcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.ui.Activator;
import net.sf.sveditor.ui.ISVIcons;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.swt.graphics.Image;

public class SVCompletionProcessor implements IContentAssistProcessor {

	private SVEditor fEditor;

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

		try {
			int lineno = 0;

			lineno = doc.getLineOfOffset(start);
			System.out.println("lineno=" + lineno);

			SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
					fEditor.getSVDBFile(), lineno);

			System.out.println("src_scope=" + src_scope);

			int c = -1, last_c = -1, idx = offset - 1;

			// Scan backwards to an activation character or the beginning of
			// line
			while (idx >= viewer.getTopIndexStartOffset()) {
				c = doc.getChar(idx);

				if (c == '.' || c == '`' || (c == ':' && last_c == ':')
						|| c == '\n') {
					break;
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

				findPreProcProposals(root, trigger, pre, start, proposals);

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
				// No recognizable trigger character, so set 'pre' based on
				// seeking backwards from the offset passed in
				idx = offset - 1;

				while (idx >= viewer.getTopIndexStartOffset()
						&& !Character.isWhitespace(doc.getChar(idx))) {
					idx--;
				}

				start = idx + 1;
				pre = doc.get(idx + 1, offset - idx - 1).trim();

				findUntriggeredProposal(viewer.getDocument(), root, trigger,
						pre, start, proposals);
			}

		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		order_proposals(proposals);
		return proposals.toArray(new ICompletionProposal[proposals.size()]);
	}

	/**
	 * order_proposals()
	 * 
	 * Re-order the proposals to be in alphabetical order
	 * 
	 * @param proposals
	 */
	private void order_proposals(List<ICompletionProposal> proposals) {
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
	private void findUntriggeredProposal(IDocument doc, String root,
			String trigger, String pre, int start,
			List<ICompletionProposal> proposals) {
		SVDBProjectData pd = fEditor.getProjectData();
		SVDBIndexSearcher searcher = new SVDBIndexSearcher();

		// Add the live version of the file to the search
		searcher.addFile(fEditor.getSVDBFile());
		searcher.addIndex(pd.getFileIndex());

		int lineno = 0;

		try {
			lineno = doc.getLineOfOffset(start);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				fEditor.getSVDBFile(), lineno);

		// Figure out which scope we're in and collect info from there...

		// Begin working outwards
		while (src_scope != null) {
			System.out.println("type=" + src_scope.getType() + " name="
					+ src_scope.getName());

			// TODO: Search this scope and enclosing scopes for functions,
			// tasks, and variables
			// TODO: If one of the enclosing scopes is a class scope, then
			// search the base-class tree as well
			addMatchingTasksVars(src_scope, doc, root, trigger, pre, start,
					proposals);

			if (src_scope.getType() == SVDBItemType.Class) {
				addClassHierarchyItems(searcher,
						(SVDBModIfcClassDecl) src_scope, doc, root, trigger,
						pre, start, proposals);
			}

			src_scope = src_scope.getParent();
		}

		for (SVDBItem it : fEditor.getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function) {
				if (it.getName() != null
						&& (pre.equals("") || it.getName().startsWith(pre))) {
					Image img = SVDBIconUtils.getIcon(it);
					proposals.add(new CompletionProposal(it.getName(), start,
							pre.length(), it.getName().length(), img, null,
							null, null));
				}
			} else if (it.getType() == SVDBItemType.Module
					|| it.getType() == SVDBItemType.Class) {
				// TODO: recurse and search the scope for this
			}
		}

		if (pd != null) {
			// Collect all matching class names from the build path
			for (SVDBFile f : pd.getFileIndex().getFileList()) {
				for (SVDBItem it : f.getItems()) {
					if (it.getType() == SVDBItemType.Class) {
						if (it.getName() != null
								&& (pre.equals("") || it.getName().startsWith(
										pre))) {
							Image img = SVDBIconUtils.getIcon(it);
							ICompletionProposal p = new CompletionProposal(it
									.getName(), start, pre.length(), it
									.getName().length(), img, null, null, null);
							addProposal(p, proposals);
						}
					} else if (it.getType() == SVDBItemType.PackageDecl) {
					}
				}
			}
		}
	}

	private void findTriggeredProposals(
			ITextViewer			viewer,
			SVDBScopeItem		src_scope,
			int					pre_trigger_idx,
			String				trigger,
			String				pre,
			int					start,
			List<ICompletionProposal> proposals) {
		SVDBProjectData pd = fEditor.getProjectData();
		SVDBIndexSearcher searcher = new SVDBIndexSearcher();
		
		// Add the live version of the file to the search
		searcher.addFile(fEditor.getSVDBFile());
		searcher.addIndex(pd.getFileIndex());
		
		String preTrigger = extractPreTriggerPortion(
				viewer, pre_trigger_idx);
		
		ProcessPreTriggerInfo info = processPreTriggerPortion(
				searcher, src_scope, preTrigger);
		
		List<SVDBItem> result = new ArrayList<SVDBItem>();
		
		if (info.item != null && info.item instanceof SVDBScopeItem) {
			result.addAll(searcher.findByPrefixInTypeHierarchy(
					pre, (SVDBScopeItem)info.item)); 
		}
		
		for (SVDBItem it : result) {
			Image img = SVDBIconUtils.getIcon(it);
			proposals.add(new CompletionProposal(it.getName(), start,
					pre.length(), it.getName().length(), img, null,
					null, null));
		}
	}

	private String extractPreTriggerPortion(ITextViewer viewer,
			int pre_trigger_idx) {
		IDocument doc = viewer.getDocument();
		StringBuffer tmp = new StringBuffer();
		int last_nws_ch = -1;
		String end_match[] = { "nde", // end
				"nigeb", // begin
				";" };
		int idx = pre_trigger_idx;

		try {
			while (idx >= 0) {
				int ch = -1;
				// Skip whitespace
				while (idx >= 0
						&& Character.isWhitespace((ch = doc.getChar(idx)))) {
					idx--;
				}

				if (idx < 0) {
					break;
				}

				if (ch == '(') {
					break;
				} else if (ch == ')') {
					if (last_nws_ch != '.' && last_nws_ch != ':'
							&& last_nws_ch != -1) {
						break;
					}

					int matchLevel = 1;

					tmp.append((char) ch);

					// Otherwise, skip matching braces
					while (matchLevel > 0 && --idx >= 0) {
						// next char
						ch = doc.getChar(idx);
						if (ch == ')') {
							matchLevel++;
						} else if (ch == '(') {
							matchLevel--;
						}
						tmp.append((char) ch);
					}
				} else {
					tmp.append((char) ch);
				}

				last_nws_ch = ch;
				idx--;

				boolean found_end = false;
				for (int i = 0; i < end_match.length; i++) {
					if (tmp.toString().endsWith(end_match[i])) {
						tmp.setLength(tmp.length() - end_match[i].length());
						found_end = true;
						break;
					}
				}

				if (found_end) {
					break;
				}
			}
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		return tmp.reverse().toString();
	}

	private class MutableIdx {
		int val;
	}

	private class ProcessPreTriggerInfo {
		int 		qualifiers = 0;
		SVDBItem 	item;
	}

	private ProcessPreTriggerInfo processPreTriggerPortion(
			SVDBIndexSearcher searcher, SVDBScopeItem context, String preTrigger) {
		MutableIdx idx = new MutableIdx();
		idx.val = 0;

		return processPreTriggerPortion(null, searcher, context, preTrigger, idx);
	}

	/**
	 *
	 * TODO: It would probably help if we maintained some type of 
	 * data structure as a type reference. Problems arise when we
	 * reference a type whose elements depend on context. 
	 * 
	 * For example, if we have a parameterized class and one of
	 * the functions return type is parameterized. In this case, 
	 * it would be nice to have a unique object to represent the 
	 * parameterized class
	 * 
	 * 
	 * The procedure here is pretty simple:
	 * - Read an identifier
	 *   - Determine whether it is a function, variable, or cast
	 *       - If a cast, lookup the type
	 *       - else if first lookup, lookup starting from current scope 
	 *           and look through hierarchy
	 *       - else lookup id in last-located type  
	 * 
	 * @param searcher
	 * @param context
	 * @param preTrigger
	 * @param idx
	 * @return
	 * 
	 */
	private ProcessPreTriggerInfo processPreTriggerPortion(
			String				preceeding_activator,
			SVDBIndexSearcher 	searcher, 
			SVDBScopeItem 		context,
			String 				preTrigger, 
			MutableIdx 			idx) {
		String id = null;
		ProcessPreTriggerInfo ret = new ProcessPreTriggerInfo();

		// Need to make some changes to track the preceeding character, not the
		// next. For example, if the preceeding character was '.', then we should
		// look for id() within typeof(ret.item)
		while (idx.val < preTrigger.length() && ret != null) {
			int ch = preTrigger.charAt(idx.val);

			if (ch == '(') {
				// recursively expand
				idx.val++;
				ret = processPreTriggerPortion(preceeding_activator,
						searcher, context, preTrigger, idx);
				
				// Give up because the lower-level parser did...
				if (ret == null) {
					break;
				}

				// Assert that on return, idx references ')'
				/*
				 * if (idx.val < preTrigger.length() ||
				 * preTrigger.charAt(idx.val) != ')') {
				 * System.out.println("[ERROR] unterminated ()"); }
				 */
				// idx.val++;
			} else if (ch == '.') {
				// use the preceeding
				preceeding_activator = ".";
			} else if (ch == ':' && 
					idx.val+1 < preTrigger.length() && 
					preTrigger.charAt(idx.val+1) == ':') {
				idx.val++;
				preceeding_activator = "::";
			} else if (Character.isJavaIdentifierPart(ch)) {
				// Read an identifier
				StringBuffer tmp = new StringBuffer();

				tmp.append((char) ch);
				while (++idx.val < preTrigger.length()
						&& Character.isJavaIdentifierPart(
								(ch = preTrigger.charAt(idx.val)))) {
					tmp.append((char) ch);
				}
				id = tmp.toString();
				
				System.out.println("id=" + id + " ch after id=" + (char)ch);

				if (ch == '(' || ch == '\'') {
					if (ch == '(') {
						// lookup id as a function
						System.out.println("Look for function \"" + id + "\"");

						// TODO: must use scoped lookup by whatever preceeded
						List<SVDBItem> matches = null;

						// If we have a previous lookup match earlier in the completion
						// string, then we should use that information to lookup this 
						// portion
						SVDBItem search_ctxt = (ret.item != null)?ret.item:context;

						// Browse up the search context to reach the class scope
						// TODO: Also want to support package-scope items (?)
						while (search_ctxt != null && search_ctxt.getType() != SVDBItemType.Class) {
							search_ctxt = search_ctxt.getParent();
						}
						
						if (search_ctxt != null) {
							matches = searcher.findByNameInClassHierarchy(
									id, (SVDBScopeItem)search_ctxt, 
									SVDBItemType.Function);
						}

						if (matches != null && matches.size() > 0) {
							SVDBTaskFuncScope func = (SVDBTaskFuncScope)matches.get(0);
							SVDBModIfcClassDecl cl = searcher.findNamedClass(func.getReturnType());

							if (matches.size() > 1) {
								System.out.println("[WARN] Taking first "
										+ "item in search for \"" + id + "\"");
							}

							System.out.println("return type \"" + id + "\" is: " + cl);
							ret.item = cl;
							
							// No point in continuing, since we've lost the trail
							if (cl == null) {
								ret = null;
								break;
							}
						}
					} else {
						// ' indicates this is a type name
						// TODO: We don't yet have the infrastructure to deal with types
						List<SVDBItem> result = searcher.findByName(id,
								SVDBItemType.Class, SVDBItemType.Struct);

						if (result.size() > 0) {
							SVDBTaskFuncScope func = (SVDBTaskFuncScope)result.get(0);
							ret.item = result.get(0);

							if (result.size() > 1) {
								System.out.println("[WARN] Lookup of \"" + id
										+ "\" resulted in " + result.size()
										+ " matches");
							}
						} else {
							ret = null;

							// No point in continuing. We've failed to find a
							// match
							break;
						}

						idx.val++;
					}

					// Skip '()'
					// In both the case of a function/task call or a cast, 
					// we can ignore what's in the parens
					int matchLevel = 1;

					while (++idx.val < preTrigger.length() && matchLevel > 0) {
						ch = preTrigger.charAt(idx.val);
						if (ch == '(') {
							matchLevel++;
						} else if (ch == ')') {
							matchLevel--;
						}
					}
					idx.val++;
				} else {
					// 
					if (ret.item == null) {
						// First element, so we need to lookup the item
						SVDBScopeItem tmp_context = context;
						
						while (tmp_context != null && ret.item == null) {
							for (SVDBItem it : tmp_context.getItems()) {
								if (it.getName().equals(id)) {
									ret.item = it;
									break;
								}
							}
							tmp_context = tmp_context.getParent();
						}
					} else {
						// Lookup what follows based on the trigger
						// Search up hierarchy
						// searcher.findByNameInClassHierarchy(id, ret.item);
					}
				}
			} else {
				// TODO: This is actually an error (?)
				
				// The identifier just read is not a function call
				// Adjust the index based on the type of completion character
				if (ch == ':'					
					&& (idx.val + 1 < preTrigger.length() && preTrigger
						.charAt(idx.val + 1) == ':')) {
					idx.val += 2;
				} else if (ch == '.') {
					idx.val++;
				} else {
					System.out.println("other: ch=" + (char) ch);
					idx.val++;
				}
				
				// Now, do a bit of searching to figure out what this is
				boolean found = false;
				if (ret.item == null && 
						(context.getType() == SVDBItemType.Function ||
								context.getType() == SVDBItemType.Task)) {
					// If the item is null, then this is the first 
					// element in the expression. When this is the case, 
					// we want to start our search by looking at the task/func
					// parameters and local variables

					List<SVDBItem> vars = searcher.findVarsByNameInScopes(
							id, context, true);

					if (vars.size() > 0) {
						ret.item = searcher.findClassTypeOfItem(vars.get(0));
						found = true;
						break;
					}
					
					if (!found) {
						// Also look at task/function parameters
						for (SVDBItem it : ((SVDBTaskFuncScope)context).getParams()) {
							if (it.getName().equals(id)) {
								ret.item = it;
								found = true;
								break;
							}
						}
					}
					
					if (found) {
						
					}
				}
				
				if (!found) {
					// Use ret.item as a type
				}
				
				if (!found) {
					// okay, we failed to find anything meaningful
					ret = null;
					break;
				}
			}
		}

		return ret;
	}

	private void addMatchingTasksVars(SVDBScopeItem src_scope, IDocument doc,
			String root, String trigger, String pre, int start,
			List<ICompletionProposal> proposals) {

		for (SVDBItem it : src_scope.getItems()) {
			if (it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function
					|| it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.TaskFuncParam) {
				if (it.getName().startsWith(pre)) {
					Image img = SVDBIconUtils.getIcon(it);
					addProposal(new CompletionProposal(it.getName(), start, pre
							.length(), it.getName().length(), img, null, null,
							null), proposals);
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
	private void addClassHierarchyItems(SVDBIndexSearcher searcher,
			SVDBModIfcClassDecl src_scope, IDocument doc, String root,
			String trigger, String pre, int start,
			List<ICompletionProposal> proposals) {

		while (true) {
			System.out.println("src_scope=" + src_scope.getName()
					+ " superClass=" + src_scope.getSuperClass());
			SVDBModIfcClassDecl src_scope_t = src_scope;
			if (src_scope.getSuperClass() == null
					|| (src_scope = searcher.findNamedClass(src_scope
							.getSuperClass())) == null) {
				System.out.println("End expansion: " + src_scope_t.getName());
				System.out.println("    SuperClass="
						+ src_scope_t.getSuperClass());
				System.out.println("    Find="
						+ searcher.findNamedClass(src_scope_t.getSuperClass()));
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
	private void findPreProcProposals(String root, String trigger, String pre,
			int start, List<ICompletionProposal> proposals) {
		SVDBProjectData pd = fEditor.getProjectData();

		if (pd != null) {
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
				for (SVDBFile f : pd.getFileIndex().getFileList()) {
					File file = new File(f.getName());
					if (file.getName().startsWith(post_include)) {
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
						addProposal(new CompletionProposal(replacement,
										start, replacement_length,
										replacement.length(), 
										Activator.getImage(ISVIcons.INCLUDE_OBJ),
										display, null, null), proposals);
					}
				}
			} else {
				for (String p : fBuiltInMacroProposals) {
					if (p.startsWith(pre)) {
						addProposal(new CompletionProposal(p, start, pre
								.length(), p.length()), proposals);
					}
				}
				// Collect matching macro names from the build path
				for (SVDBFile f : pd.getFileIndex().getFileList()) {
					for (SVDBItem it : f.getItems()) {
						if (it.getType() == SVDBItemType.Macro) {
							if (it.getName() != null
									&& (pre.equals("") || it.getName()
											.startsWith(pre))) {
								Image img = SVDBIconUtils.getIcon(it);
								addProposal(new CompletionProposal(
										it.getName(), start, pre.length(), it
												.getName().length(), img, null,
										null, null), proposals);
							}
						}
					}
				}
			}
		}
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

	public IContextInformation[] computeContextInformation(ITextViewer viewer,
			int offset) {
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

}
