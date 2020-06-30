

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
 *     Armond Paiva - repurposed for use in SVEditor quick views
 *******************************************************************************/

package org.eclipse.hdt.sveditor.ui.text;

import org.eclipse.hdt.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.information.IInformationProvider;
import org.eclipse.jface.text.information.IInformationProviderExtension;

import org.eclipse.ui.IEditorPart;

/**
 * Provides the editor as information for controls that don't need anything more specific
 */
public class SVEditorProvider implements IInformationProvider, IInformationProviderExtension {

	private SVEditor fEditor;

	public SVEditorProvider(IEditorPart editor) {
		if (editor instanceof SVEditor)
			fEditor= (SVEditor)editor;
	}

	public SVEditorProvider(IEditorPart editor, boolean useCodeResolve) {
		this(editor);
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
		return fEditor ;
	}

	public IRegion getSubject(ITextViewer textViewer, int offset) {
		if (textViewer != null && fEditor != null) {
			// Unused... but we've got to return non-null as 
			// there has to be a subject 
			return new Region(offset, 0);
		}
		return null ;
	}
}
