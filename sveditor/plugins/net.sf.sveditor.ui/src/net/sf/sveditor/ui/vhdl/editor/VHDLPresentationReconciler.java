package net.sf.sveditor.ui.vhdl.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.PresentationReconciler;

public class VHDLPresentationReconciler extends PresentationReconciler {
	private IDocument			fLastDocument;

	/*
	@Override
	protected TextPresentation createPresentation(IRegion damage,
			IDocument document) {
		if (document != fLastDocument) {
			setDocumentToDamagers(document);
			setDocumentToRepairers(document);
			
			fLastDocument = document;
		}
		
		return super.createPresentation(damage, document);
	}
	 */
	
	
	

}
