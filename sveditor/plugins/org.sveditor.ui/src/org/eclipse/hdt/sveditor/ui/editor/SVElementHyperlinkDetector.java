/*******************************************************************************
 * Copyright (c) 2000, 2012 IBM Corporation and others.
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
 *     Armond Paiva - repurposed from JDT for use in SVEditor
 *******************************************************************************/
package org.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;

import org.sveditor.ui.SVUiPlugin;
import org.sveditor.ui.editor.actions.OpenDeclarationAction;
import org.sveditor.ui.editor.actions.OpenTypeHierarchyAction;
import org.sveditor.ui.editor.actions.SelectionConverter;
import org.sveditor.ui.text.SVWordFinder;

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.log.ILogLevel;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.hyperlink.AbstractHyperlinkDetector;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;


public class SVElementHyperlinkDetector extends AbstractHyperlinkDetector implements ILogLevel {
	
	private LogHandle	fLog ;
	
	public SVElementHyperlinkDetector() {
		fLog = LogFactory.getLogHandle("ElementHyperlinkDetector") ;
	}

	public IHyperlink[] detectHyperlinks(ITextViewer textViewer, IRegion region, boolean canShowMultipleHyperlinks) {
		
		ITextEditor textEditor= (ITextEditor)getAdapter(ITextEditor.class) ;
		
		if (region == null || !(textEditor instanceof SVEditor)) return null;
		
		SVEditor editor = (SVEditor)textEditor ;
		
		int offset= region.getOffset();
		
		fLog.debug(LEVEL_MIN, "Detecting hyperlinks") ;
		
		ISVDBItemBase item = SelectionConverter.getElementAt(editor, offset) ;
		
		if(item == null) {
			return null ;
		}
		
		IDocumentProvider documentProvider= editor.getDocumentProvider();
		IEditorInput editorInput= editor.getEditorInput();
		IDocument document= documentProvider.getDocument(editorInput);
		IRegion wordRegion = SVWordFinder.findWord(document, offset) ;
		
		return createHyperLinks(editor, item, wordRegion) ;
		
		
	}
	
	private IHyperlink[] createHyperLinks(SVEditor editor, ISVDBItemBase item, IRegion wordRegion) {
		
		List<IHyperlink> links = new ArrayList<IHyperlink>() ;
		
		ResourceBundle bundle = SVUiPlugin.getDefault().getResources() ;
		
		fLog.debug(LEVEL_MIN, "Creating links for type(" + item.getType() + ")") ;
		
		switch(item.getType()) {
			case ClassDecl:
				// open decl
				Action action = new OpenDeclarationAction(bundle, editor) ;
				links.add(new SVElementHyperlink(wordRegion, action, item, false, "Open Declaration")) ;
				// open hierarchy
				action = new OpenTypeHierarchyAction(bundle, editor) ;
				links.add(new SVElementHyperlink(wordRegion, action, item, false, "Open Type Hierarchy")) ;
				break ;
			default:
		}
		
		
		if(links.isEmpty()) {
			return null ;
		} else {
			return links.toArray(new IHyperlink[links.size()]) ;
		}

	}

	@Override
	public void dispose() {
		super.dispose();
	}


}
