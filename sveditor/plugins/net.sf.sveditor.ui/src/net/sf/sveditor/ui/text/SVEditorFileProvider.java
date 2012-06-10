

/*******************************************************************************
 * Copyright (c) 2000, 2010 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed for use in SVEDitor quick views
 *******************************************************************************/

package net.sf.sveditor.ui.text;

import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.information.IInformationProvider;
import org.eclipse.jface.text.information.IInformationProviderExtension;

import org.eclipse.ui.IEditorPart;

/**
 * Provides a Java element to be displayed in by an information presenter.
 */
public class SVEditorFileProvider implements IInformationProvider, IInformationProviderExtension {

	private SVEditor fEditor;

	public SVEditorFileProvider(IEditorPart editor) {
		if (editor instanceof SVEditor)
			fEditor= (SVEditor)editor;
	}

	public SVEditorFileProvider(IEditorPart editor, boolean useCodeResolve) {
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
		if (fEditor == null)
			return null;
		return fEditor.getSVDBFile() ;
	}

	@Override
	public IRegion getSubject(ITextViewer textViewer, int offset) {
		if (textViewer != null && fEditor != null) {
			// Unused... but we've got to return non-null as 
			// there has to be a subject 
			return new Region(offset, 0);
		}
		return null ;
	}
}
