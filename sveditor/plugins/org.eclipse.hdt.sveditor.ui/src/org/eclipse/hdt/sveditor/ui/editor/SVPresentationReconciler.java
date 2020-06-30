/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
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
