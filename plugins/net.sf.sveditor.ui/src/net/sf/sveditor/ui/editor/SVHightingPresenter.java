/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.ITextPresentationListener;
import org.eclipse.jface.text.TextPresentation;

public class SVHightingPresenter implements ITextPresentationListener,
		ITextInputListener, IDocumentListener {

	
	public void applyTextPresentation(TextPresentation textPresentation) {
		// TODO Auto-generated method stub

	}

	
	public void inputDocumentAboutToBeChanged(IDocument oldInput,
			IDocument newInput) {
		System.out.println("inputDocumentAboutToBeChanged()");
		// TODO Auto-generated method stub

	}

	
	public void inputDocumentChanged(IDocument oldInput, IDocument newInput) {
		// TODO Auto-generated method stub
		System.out.println("inputDocumentChanged()");

	}

	
	public void documentAboutToBeChanged(DocumentEvent event) {
		// TODO Auto-generated method stub

	}

	
	public void documentChanged(DocumentEvent event) {
		// TODO Auto-generated method stub
		System.out.println("documentChanged()");

	}

}
