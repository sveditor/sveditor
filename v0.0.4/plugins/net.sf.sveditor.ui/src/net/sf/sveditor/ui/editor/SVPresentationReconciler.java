package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.presentation.PresentationReconciler;

public class SVPresentationReconciler extends PresentationReconciler {
	private IDocument			fLastDocument;
	
	
	public TextPresentation createRepairDescription(IRegion damage, IDocument doc) {
		if (doc != fLastDocument) {
			setDocumentToDamagers(doc);
			setDocumentToRepairers(doc);
			fLastDocument = doc;
		}
		return createPresentation(damage, doc);
	}

}
