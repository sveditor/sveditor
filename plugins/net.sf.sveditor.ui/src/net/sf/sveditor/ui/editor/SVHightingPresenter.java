package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.ITextPresentationListener;
import org.eclipse.jface.text.TextPresentation;

public class SVHightingPresenter implements ITextPresentationListener,
		ITextInputListener, IDocumentListener {

	@Override
	public void applyTextPresentation(TextPresentation textPresentation) {
		// TODO Auto-generated method stub

	}

	@Override
	public void inputDocumentAboutToBeChanged(IDocument oldInput,
			IDocument newInput) {
		System.out.println("inputDocumentAboutToBeChanged()");
		// TODO Auto-generated method stub

	}

	@Override
	public void inputDocumentChanged(IDocument oldInput, IDocument newInput) {
		// TODO Auto-generated method stub
		System.out.println("inputDocumentChanged()");

	}

	@Override
	public void documentAboutToBeChanged(DocumentEvent event) {
		// TODO Auto-generated method stub

	}

	@Override
	public void documentChanged(DocumentEvent event) {
		// TODO Auto-generated method stub
		System.out.println("documentChanged()");

	}

}
