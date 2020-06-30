/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.ui.argfile.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.ui.scanutils.SVArgFileDocumentTextScanner;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.argfile.content_assist.AbstractArgFileCompletionProcessor;
import org.eclipse.hdt.sveditor.core.argfile.content_assist.SVArgFileCompletionProposal;
import org.eclipse.hdt.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;

public class SVArgFileCompletionProcessor extends AbstractArgFileCompletionProcessor 
	implements IContentAssistProcessor {
	
	private static final char[] PROPOSAL_ACTIVATION_CHARS = { '/', '\\' };	
	private final IContextInformation NO_CONTEXTS[] = new IContextInformation[0];
	private SVArgFileEditor					fEditor;
	
	public SVArgFileCompletionProcessor(SVArgFileEditor editor) {
		super(LogFactory.getLogHandle("SVArgFileCompletionProcessor"));
		fEditor = editor;
	
	}

	public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int offset) {
		SVArgFileDocumentTextScanner scanner = new SVArgFileDocumentTextScanner(
				viewer.getDocument(), offset);
		scanner.setSkipComments(true);
		
		Tuple<String, ISVArgFileVariableProvider> ctxt = fEditor.findArgFileContext();
		
		init(new SVDBWSFileSystemProvider(), ctxt.first(), null, ctxt.second());
	
		int lineno = -1, linepos = -1;
		
		try {
			lineno = viewer.getDocument().getLineOfOffset(offset);
			linepos = (offset-viewer.getDocument().getLineOffset(lineno));
		} catch (BadLocationException e) {
			e.printStackTrace();
			return new ICompletionProposal[0];
		}
		
		computeProposals(scanner, lineno, linepos);
		
		List<ICompletionProposal> cp_l = new ArrayList<ICompletionProposal>();
		
		for (SVArgFileCompletionProposal p : fProposals) {
			List<ICompletionProposal> cp = convertToProposal(p, viewer.getDocument());
			cp_l.addAll(cp);
		}
		
		return cp_l.toArray(new ICompletionProposal[cp_l.size()]);
	}
	
	protected List<ICompletionProposal> convertToProposal(
			SVArgFileCompletionProposal			p,
			IDocument							doc) {
		List<ICompletionProposal> ret = new ArrayList<ICompletionProposal>();
		ICompletionProposal cp = null;

		int replacementOffset = p.getReplacementOffset();
		int replacementLength = p.getReplacementLength();
		
		// Patch up to ensure the replacement offset doesn't extend beyond the document
		if (replacementOffset > doc.getLength()) {
			replacementOffset = doc.getLength();
		}
	
		/** TODO:
		String doc_str = "";
		try {
			doc_str = doc.get(0, replacementOffset);
		} catch (BadLocationException e) {}
		 */
		
		cp = new CompletionProposal(p.getReplacement(), 
				replacementOffset, replacementLength, 
				p.getReplacement().length());
		
		if (cp != null) {
			ret.add(cp);
		}
		
		return ret;
	}

	public IContextInformation[] computeContextInformation(ITextViewer viewer, int offset) {
		return NO_CONTEXTS;
	}

	public char[] getCompletionProposalAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	public char[] getContextInformationAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	public String getErrorMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	public IContextInformationValidator getContextInformationValidator() {
		// TODO Auto-generated method stub
		return null;
	}
	
}
