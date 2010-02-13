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
