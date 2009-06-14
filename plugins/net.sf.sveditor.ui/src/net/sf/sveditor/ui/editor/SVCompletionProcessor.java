package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;

public class SVCompletionProcessor extends AbstractCompletionProcessor 
		implements IContentAssistProcessor {

	private SVEditor 	fEditor;

	private static final char[] PROPOSAL_ACTIVATION_CHARS = { '.', ':' };
	private final IContextInformation NO_CONTEXTS[] = new IContextInformation[0];
	
	private List<ICompletionProposal>				fProposals = 
		new ArrayList<ICompletionProposal>();

	
	public void init(SVEditor editor) {
		fEditor = editor;
	}
	
	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer viewer, int offset) {
		fProposals.clear();
		SVDocumentTextScanner scanner = new SVDocumentTextScanner(
				viewer.getDocument(), offset);
		
		int lineno = -1;
		
		try {
			lineno = viewer.getDocument().getLineOfOffset(offset);
		} catch (BadLocationException e) {
			e.printStackTrace();
			return new ICompletionProposal[0];
		}
		
		computeProposals(scanner, fEditor.getSVDBFile(), lineno);
		
		// convert SVProposal list to ICompletionProposal list
		for (SVCompletionProposal p : fCompletionProposals) {
			fProposals.add(convertToProposal(p));
		}
		
		return fProposals.toArray(new ICompletionProposal[fProposals.size()]);
	}
	
	protected ICompletionProposal convertToProposal(SVCompletionProposal p) {
		ICompletionProposal cp = null;
		
		return cp;
	}
	
	
	@Override
	protected ISVDBIndexIterator getIndexIterator() {
		return fEditor.getIndexIterator();
	}

	@Override
	protected SVDBFile getSVDBFile() {
		return fEditor.getSVDBFile();
	}


	/**
	 * Add a proposal to the proposals list, ensure that this proposal isn't a
	 * duplicate
	 * 
	 * @param p
	 * @param proposals
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
	 */
	
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
