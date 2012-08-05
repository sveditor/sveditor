/*******************************************************************************
 * Copyright (c) 2000, 2012 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Brock Janiczak <brockj@tpg.com.au> - [implementation] Streams not being closed in Javadoc views - https://bugs.eclipse.org/bugs/show_bug.cgi?id=214854
 *     Armond Paiva - repurposed from JDT for use in SVEditor
 *******************************************************************************/
package net.sf.sveditor.ui.text.hover;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.actions.SelectionConverter;
import net.sf.sveditor.ui.text.SVWordFinder;

import org.eclipse.swt.widgets.Shell;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHoverExtension;
import org.eclipse.jface.text.ITextHoverExtension2;
import org.eclipse.jface.text.ITextViewer;

import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;

import org.eclipse.ui.editors.text.EditorsUI;

/*

import org.eclipse.jdt.core.ICodeAssist;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.ITypeRoot;
import org.eclipse.jdt.core.JavaModelException;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jdt.ui.text.java.hover.IJavaEditorTextHover;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.IClassFileEditorInput;
import org.eclipse.jdt.internal.ui.javaeditor.WorkingCopyManager;
import org.eclipse.jdt.internal.ui.text.JavaWordFinder;

*/

/**
 * Abstract class for providing hover information for Java elements.
 *
 */
public abstract class AbstractSVEditorTextHover implements ISVEditorTextHover, ITextHoverExtension, ITextHoverExtension2 {
	private IEditorPart fEditor;

	/*
	 * @see IJavaEditorTextHover#setEditor(IEditorPart)
	 */
	public void setEditor(IEditorPart editor) {
		fEditor= editor;
	}

	protected IEditorPart getEditor() {
		return fEditor;
	}
	
	/*

	protected ICodeAssist getCodeAssist() {
		if (fEditor != null) {
			IEditorInput input= fEditor.getEditorInput();
			if (input instanceof IClassFileEditorInput) {
				IClassFileEditorInput cfeInput= (IClassFileEditorInput) input;
				return cfeInput.getClassFile();
			}

			WorkingCopyManager manager= JavaPlugin.getDefault().getWorkingCopyManager();
			return manager.getWorkingCopy(input, false);
		}

		return null;
	}
	
	*/

    /*
	 * @see org.eclipse.jface.text.ITextHoverExtension2#getHoverInfo2(org.eclipse.jface.text.ITextViewer, org.eclipse.jface.text.IRegion)
	 */
	public Object getHoverInfo2(ITextViewer textViewer, IRegion hoverRegion) {
		return getHoverInfo(textViewer, hoverRegion);
	}

	/*
	 * @see ITextHover#getHoverRegion(ITextViewer, int)
	 */
	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		return SVWordFinder.findWord(textViewer.getDocument(), offset);
	}

	/**
	 * Returns the SVDBItems elements at the given hover region.
	 *
	 * @param textViewer the text viewer
	 * @param hoverRegion the hover region
	 * @return the array with the SV elements or <code>null</code>
	 */
	protected ISVDBItemBase getSVElementAt(ITextViewer textViewer, IRegion hoverRegion) {
		/*
		 * The region should be a word region an not of length 0.
		 * This check is needed because codeSelect(...) also finds
		 * the Java element if the offset is behind the word.
		 */
		if (hoverRegion.getLength() == 0)
			return null;
		
//		IDocument document= textViewer.getDocument();
//		if (document != null && isInheritDoc(document, hoverRegion))
//			return null;

//		ICodeAssist resolve= getCodeAssist();
//		if (resolve != null) {
//			try {
//				return resolve.codeSelect(hoverRegion.getOffset(), hoverRegion.getLength());
//			} catch (JavaModelException x) {
//				return null;
//			}
//		}
		
		return SelectionConverter.getElementAt((SVEditor)fEditor, hoverRegion.getOffset()) ;
		
	}

//	/**
//	 * Returns whether the word is "inheritDoc".
//	 * 
//	 * @param document the document
//	 * @param wordRegion the word region
//	 * @return <code>true</code> iff the word is "inheritDoc"
//	 * @since 3.7
//	 */
//	private static boolean isInheritDoc(IDocument document, IRegion wordRegion) {
//		try {
//			String word= document.get(wordRegion.getOffset(), wordRegion.getLength());
//			return "inheritDoc".equals(word); //$NON-NLS-1$
//		} catch (BadLocationException e) {
//			return false;
//		}
//	}

	/*
	 * @see ITextHoverExtension#getHoverControlCreator()
	 * @since 3.0
	 */
	public IInformationControlCreator getHoverControlCreator() {
		return new IInformationControlCreator() {
			public IInformationControl createInformationControl(Shell parent) {
				return new DefaultInformationControl(parent, EditorsUI.getTooltipAffordanceString());
			}
		};
	}

	/**
	 * Delegate method for {@link JavaInformationProvider#getInformationPresenterControlCreator()}
	 * 
	 * @return the information control creator or null if none is available
	 * @since 3.4
	 */
	public IInformationControlCreator getInformationPresenterControlCreator() {
		return new IInformationControlCreator() {
			public IInformationControl createInformationControl(Shell shell) {
				return new DefaultInformationControl(shell, true);
			}
		};
	}

//	protected ITypeRoot getEditorInputJavaElement() {
//		IEditorPart editor= getEditor();
//		if (editor != null)
//			return JavaUI.getEditorInputTypeRoot(editor.getEditorInput());
//		return null;
//	}
}
