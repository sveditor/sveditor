

/*******************************************************************************
 * Copyright (c) 2000, 2010 IBM Corporation and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed for use in SVEditor
 *******************************************************************************/

package net.sf.sveditor.ui.text;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.actions.SelectionConverter;

import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.information.IInformationProvider;
import org.eclipse.jface.text.information.IInformationProviderExtension;

import org.eclipse.ui.IEditorPart;

/**
 * Provides a System Verilog element to be displayed in by an information presenter.
 */
public class SVElementProvider implements IInformationProvider, IInformationProviderExtension {

	private SVEditor fEditor;

	public SVElementProvider(IEditorPart editor) {
		if (editor instanceof SVEditor)
			fEditor= (SVEditor)editor;
	}

	/*
	 * @see IInformationProvider#getSubject(ITextViewer, int)
	 */
	public IRegion getSubject(ITextViewer textViewer, int offset) {
		if (textViewer != null && fEditor != null) {
			return new Region(offset, 0);
		}
		return null;
	}

	/*
	 * @see IInformationProvider#getInformation(ITextViewer, IRegion)
	 */
	public String getInformation(ITextViewer textViewer, IRegion subject) {
		return getInformation2(textViewer, subject).toString();
	}

	/*
	 * @see IInformationProviderExtension#getElement(ITextViewer, IRegion)
	 */
	public Object getInformation2(ITextViewer textViewer, IRegion subject) {
		if (fEditor == null)
			return null;
		
		ISVDBItemBase element = SelectionConverter.getElementAtOffset(fEditor) ;
		
		return element ;
	}
	
}
