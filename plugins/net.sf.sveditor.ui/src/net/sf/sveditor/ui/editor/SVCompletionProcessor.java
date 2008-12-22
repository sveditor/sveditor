package net.sf.sveditor.ui.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.ui.Activator;
import net.sf.sveditor.ui.ISVIcons;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.fieldassist.IContentProposal;
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
	
	private SVEditor			fEditor;
	
	private static final char[] PROPOSAL_ACTIVATION_CHARS =
	{'.', ':'};
	private static final String 			fBuiltInMacroProposals[] = {
		"define",
		"include"
	};
	
	private final IContextInformation NO_CONTEXTS[] = 
		new IContextInformation[0];
	
	public void init(SVEditor editor) {
		fEditor = editor;
	}
	
	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer viewer, int offset) {
		
		List<ICompletionProposal> proposals = new ArrayList<ICompletionProposal>();
        
		// Prefix for the completion string
		String pre=null;
		
		// Trigger characters and string prior to the trigger (if any)
		String trigger = null, root = null;
		
		// Start marks the point just after the trigger character
		int start = offset;
		
    	IDocument doc = viewer.getDocument();
		
	    try {
	    	int c=-1, last_c = -1, idx = offset-1;
	    	
            // Scan backwards to an activation character or the beginning of line
	    	while (idx >= viewer.getTopIndexStartOffset()) {
	    		c = doc.getChar(idx);

	    		if (c == '.' || c == '`' || 
	    				(c == ':' && last_c == ':') || c == '\n') {
	    			break;
	    		}
	    		last_c = c;
	    		idx--;
	    	}
	    	
	    	if (c == '.' || c == '`') {
	    		trigger = "" + (char)c;
	    	} else if (c == ':' && last_c == ':') {
	    		trigger = "::";
	    	} else {
	    		trigger = "";
	    	}
	    	
	    	start = idx+1;

	    	if (trigger.equals("`")) {
	    		// No need to scan backwards. The stem is all we have
	    		pre = doc.get(idx+1, offset-idx-1).trim();
	    		
	    		findPreProcProposals(root, trigger, pre, start, proposals);
	    		
	    	} else if (!trigger.equals("")) {
	    		// There is a trigger, so use that as a reference point
	    		pre = doc.get(idx+1, offset-idx-1).trim();
	    		
	    		start = idx+1;

	    		// Now, look before the trigger to see what we have
	    		idx -= trigger.length();
	    		
	    		// Skip any whitespace
	    		while (idx >= viewer.getTopIndexStartOffset() &&
	    				Character.isWhitespace(doc.getChar(idx))) {
	    			idx--;
	    		}
	    		
	    		// Now, see what we have
	    		c = doc.getChar(idx);
	    		if (Character.isJavaIdentifierPart(c)) {
	    			StringBuffer s = new StringBuffer();
	    			
	    			while (idx >= viewer.getTopIndexStartOffset() &&
	    					Character.isJavaIdentifierPart((c = doc.getChar(idx)))) {
	    				s.append((char)c);
	    				idx--;
	    			}
	    			s = s.reverse();
	    			root = s.toString();
	    		} else if (c == ')') {
	    			// skip matching ()
	    			System.out.println("[TODO] skip matching braces");

	    			// Now, look to see if we have a casting type
	    		}
	    	} else {
	    		// No recognizable trigger character, so set 'pre' based on 
	    		// seeking backwards from the offset passed in
	    		idx = offset-1;
	    		
	    		while (idx >= viewer.getTopIndexStartOffset() &&
	    				!Character.isWhitespace(doc.getChar(idx))) {
	    			idx--;
	    		}
	    		
	    		start = idx+1;
	    		pre = doc.get(idx+1, offset-idx-1).trim();

	    		findUntriggeredProposal(root, trigger, pre, start, proposals);
	    	}
	    	
		} catch (BadLocationException e ) {
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
		for (int i=0; i<proposals.size(); i++) {
			ICompletionProposal p_i = proposals.get(i);
			for (int j=i+1; j<proposals.size(); j++) {
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
	 * Find a proposal based on a request for content assist that did not
	 * start with a trigger string ( . ` ::)
	 * 
	 *  These proposals are made based on the prefix string and elements
	 *  from the index
	 *  
	 * @param proposals
	 * @param pre
	 */
	private void findUntriggeredProposal(
			String				root,
			String				trigger,
			String				pre,
			int					start,
			List<ICompletionProposal> proposals) {
		SVDBProjectData pd = fEditor.getProjectData();
		System.out.println("findUntriggeredProposal()");

		// TODO: need work here. Must figure out which scope we're in and
		//       collect info from there...
		for (SVDBItem it : fEditor.getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.VarDecl || 
					it.getType() == SVDBItemType.Task ||
					it.getType() == SVDBItemType.Function) {
				if (it.getName() != null &&
						(pre.equals("") || it.getName().startsWith(pre))) {
					Image img = SVDBIconUtils.getIcon(it);
					proposals.add(new CompletionProposal(
							it.getName(), start, pre.length(), it.getName().length(),
							img, null, null, null));
				}
			} else if (it.getType() == SVDBItemType.Module ||
					it.getType() == SVDBItemType.Class) {
				// TODO: recurse and search the scope for this
			}
		}
		
		if (pd != null) {
			// Collect all matching class names from the build path
			for (SVDBFile f : pd.getFileIndex().getFileList()) {
				for (SVDBItem it : f.getItems()) {
					if (it.getType() == SVDBItemType.Class) {
						if (it.getName() != null && 
								(pre.equals("") || it.getName().startsWith(pre))) {
							Image img = SVDBIconUtils.getIcon(it);
							ICompletionProposal p = new CompletionProposal(
									it.getName(), start, pre.length(), it.getName().length(),
									img, null, null, null) ;
							addProposal(p, proposals);
						}
					} else if (it.getType() == SVDBItemType.PackageDecl) {
					}
				}
			}
		}
	}

	/**
	 * findMacros()
	 * 
	 * Find macro completion proposals
	 * 
	 * @param proposals
	 * @param pre
	 */
	private void findPreProcProposals(
			String				root,
			String				trigger,
			String				pre,
			int					start,
			List<ICompletionProposal> proposals) {
		SVDBProjectData pd = fEditor.getProjectData();
		
		if (pd != null) {
			if (pre.startsWith("include")) {
				boolean leading_quote = false, trailing_quote = false;
				String display, replacement="";
				
				// Look at the point beyond the '`include'
				String post_include = pre.substring("include".length());
				
				start += "include".length();
				
				// Now, account for any whitespace
				while (post_include.length() > 0 && Character.isWhitespace(post_include.charAt(0))) {
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
						proposals.add(new CompletionProposal(
								replacement, start, replacement_length, replacement.length(), 
								Activator.getImage(ISVIcons.INCLUDE_OBJ), display, null, null));
					}
				}
			} else {
				for (String p : fBuiltInMacroProposals) {
					if (p.startsWith(pre)) {
						addProposal(new CompletionProposal(
								p, start, pre.length(), p.length()), proposals);
					}
				}
				// Collect matching macro names from the build path
				for (SVDBFile f : pd.getFileIndex().getFileList()) {
					for (SVDBItem it : f.getItems()) {
						if (it.getType() == SVDBItemType.Macro) {
							if (it.getName() != null && 
									(pre.equals("") || it.getName().startsWith(pre))) {
								addProposal(new CompletionProposal(
										it.getName(), start, pre.length(), it.getName().length()),
										proposals);
							}
						}
					}
				}
			}
		}
	}

	/**
	 * Add a proposal to the proposals list, ensure that 
	 * this proposal isn't a duplicate
	 *  
	 * @param p
	 * @param proposals
	 */
	private static void addProposal(
			ICompletionProposal 			p, 
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

}
