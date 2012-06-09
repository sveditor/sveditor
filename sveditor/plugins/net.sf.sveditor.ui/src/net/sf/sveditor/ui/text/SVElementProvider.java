

/*******************************************************************************
 * Copyright (c) 2000, 2010 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

package net.sf.sveditor.ui.text;

//public class SVElementProvider {
//
//}

import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.information.IInformationProvider;
import org.eclipse.jface.text.information.IInformationProviderExtension;

import org.eclipse.ui.IEditorPart;

//import org.eclipse.jdt.core.IJavaElement;
//import org.eclipse.jdt.core.ITypeParameter;
//import org.eclipse.jdt.core.JavaModelException;
//
//import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
//import org.eclipse.jdt.internal.ui.javaeditor.EditorUtility;
//import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;

/**
 * Provides a Java element to be displayed in by an information presenter.
 */
public class SVElementProvider implements IInformationProvider, IInformationProviderExtension {

	private SVEditor fEditor;
	private boolean fUseCodeResolve;

	public SVElementProvider(IEditorPart editor) {
		fUseCodeResolve= false;
		if (editor instanceof SVEditor)
			fEditor= (SVEditor)editor;
	}

	public SVElementProvider(IEditorPart editor, boolean useCodeResolve) {
		this(editor);
		fUseCodeResolve= useCodeResolve;
	}

	/*
	 * @see IInformationProvider#getSubject(ITextViewer, int)
	 */
	public IRegion getSubject(ITextViewer textViewer, int offset) {
		if (textViewer != null && fEditor != null) {
//			IRegion region= JavaWordFinder.findWord(textViewer.getDocument(), offset);
			IRegion region=null ; // FIXME:
			if (region != null)
				return region;
			else
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
//		if (fEditor == null)
//			return null;
//
//		try {
//			if (fUseCodeResolve) {
//				IStructuredSelection sel= SelectionConverter.getStructuredSelection(fEditor);
//				if (!sel.isEmpty()) {
//					Object element= sel.getFirstElement();
//					if (!(element instanceof ITypeParameter))
//						return element;
//				}
//			}
//			IJavaElement element= SelectionConverter.getElementAtOffset(fEditor, false);
//			if (element != null)
//				return element;
//
//			return EditorUtility.getEditorInputJavaElement(fEditor, false);
//		} catch (JavaModelException e) {
//			return null;
//		}
		
//		return null ;
		return fEditor ; // FIXME: just want to return !null for now
	}
}
