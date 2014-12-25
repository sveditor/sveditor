/*******************************************************************************
 * Copyright (c) 2000, 2012 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Genady Beryozkin <eclipse@genady.org> - [hovering] tooltip for constant string does not show constant value - https://bugs.eclipse.org/bugs/show_bug.cgi?id=85382
 *     Armond Paiva - repurposed from JDT for use in sveditor
 *******************************************************************************/

package net.sf.sveditor.ui.text.hover;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindDocComment;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.docs.IDocTopicManager;
import net.sf.sveditor.core.docs.html.HTMLFromNDMarkup;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclResult;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.internal.text.html.HTMLPrinter;
import org.eclipse.jface.text.AbstractReusableInformationControlCreator;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchSite;
import org.osgi.framework.Bundle;

import com.sun.xml.internal.fastinfoset.AbstractResourceBundle;


/**
 * Provides Javadoc as hover info for Java elements.
 *
 * @since 2.1
 */
public class SVDocHover extends AbstractSVEditorTextHover {
	
	private LogHandle log ; 
	
	public SVDocHover() {
		log = LogFactory.getLogHandle("SVDocHover") ;
	}



	/**
	 * The hover control creator.
	 *
	 */
	private IInformationControlCreator fHoverControlCreator;
	/**
	 * The presentation control creator.
	 *
	 */
	private IInformationControlCreator fPresenterControlCreator;

	public IInformationControlCreator getInformationPresenterControlCreator() {
		if (fPresenterControlCreator == null) {
			fPresenterControlCreator = new AbstractReusableInformationControlCreator() {
				@Override
				protected IInformationControl doCreateInformationControl(Shell parent) {
					return new SVHoverInformationControl(parent);
				}
			};
		}
		return fPresenterControlCreator;
	}

	private IWorkbenchSite getSite() {
		IEditorPart editor= getEditor();
		if (editor == null) {
			IWorkbenchPage page= SVUiPlugin.getActivePage() ;
			if (page != null)
				editor= page.getActiveEditor();
		}
		if (editor != null)
			return editor.getSite();

		return null;
	}

	/*
	 * @see ITextHoverExtension#getHoverControlCreator()
	 */
	@Override
	public IInformationControlCreator getHoverControlCreator() {
		if (fHoverControlCreator == null) {
			fHoverControlCreator = new AbstractReusableInformationControlCreator() {
				
				@Override
				protected IInformationControl doCreateInformationControl(Shell parent) {
					return new SVHoverInformationDisplay(parent, 
							getInformationPresenterControlCreator());
				}
			};
		}
		return fHoverControlCreator;
	}

	/**
	 * @deprecated see {@link org.eclipse.jface.text.ITextHover#getHoverInfo(ITextViewer, IRegion)}
	 */
	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		Object info_o = getHoverInfo2(textViewer, hoverRegion);
		
		if (info_o != null && (info_o instanceof SVHoverInformationControlInput)) {
			return ((SVHoverInformationControlInput)info_o).getContent();
//			return ((SVHoverInformationControlInput)info_o).getHtml();
		} else {
			return null;
		}
	}

	/*
	 * @see org.eclipse.jface.text.ITextHoverExtension2#getHoverInfo2(org.eclipse.jface.text.ITextViewer, org.eclipse.jface.text.IRegion)
	 */
	@Override
	public Object getHoverInfo2(ITextViewer textViewer, IRegion hoverRegion) {
		List<OpenDeclResult> items = null;
		SVEditor editor = ((SVEditor)getEditor()) ;
		IDocument doc = editor.getDocument() ;
		
		int offset = hoverRegion.getOffset() ;
		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		scanner.setSkipComments(true) ;
		
		SVDBFile file = editor.getSVDBFile();
		int line = -1;
		
		try {
			line = doc.getLineOfOffset(hoverRegion.getOffset());
		} catch (BadLocationException e) {
			// Nothing to be done here
			return null;
		}
		
		SVHoverInformationControlInput ret = null;
//		Tuple<ISVDBItemBase, SVDBFile>  target = findTarget(hoverRegion);
		
		Tuple<SVExprContext, ISVDBScopeItem> context_scope = OpenDeclUtils.getContextScope(
				file, line, scanner);
		SVExprContext ctxt = context_scope.first();
		
		System.out.println("context_scope: root=" + ctxt.fRoot + " leaf=" + ctxt.fLeaf + " trigger=" + ctxt.fTrigger);
		
//		System.out.println("target=" + target);
		
		items = OpenDeclUtils.openDecl(context_scope.first(), 
				context_scope.second(), editor.getIndexIterator());
		
		if (items == null || items.size() == 0) {
			return null;
		}
		OpenDeclResult result = items.get(0);
		
		ret = new SVHoverInformationControlInput(
				result.getItem(), 
				context_scope.second(), // active scope
				editor.getIndexIterator());
		SVHoverContentProvider cp = null;
		
		if ((cp = getNaturalDocHoverContent(result, hoverRegion)) != null) {
			ret.setContentProvider(SVHoverInformationControlInput.CONTENT_DOC, cp);
		}
		
		if ((cp = getDeclarationHoverContent(result, hoverRegion)) != null) {
			ret.setContentProvider(SVHoverInformationControlInput.CONTENT_DECL, cp);
		}
		
		if ((cp = getMacroExpansionHoverContent(ctxt, result, hoverRegion)) != null) {
			
		}

		if (ret.size() > 0) {
			return ret;
		} else {
			return null;
		}
	}


	/**
	 * Computes the hover info.
	 *
	 * @param elements the resolved elements
	 * @param editorInputElement the editor input, or <code>null</code>
	 * @param hoverRegion the text range of the hovered word, or <code>null</code>
	 * @param previousInput the previous input, or <code>null</code>
	 * @return the HTML hover info for the given element(s) or <code>null</code> if no information is available
	 */
	private SVNaturalDocHoverContentProvider getNaturalDocHoverContent(
			OpenDeclResult						target,
			IRegion 							hoverRegion) {
		ISVDBItemBase element = target.getItem();
		
		if(!(element instanceof ISVDBNamedItem )) {
			return null;
		}
		
		ISVDBIndexIterator index_it = ((SVEditor)getEditor()).getSVDBIndex();
		
		// Find the doc comment corresponding to the specified element
		SVDBFindDocComment finder = new SVDBFindDocComment(index_it);
		SVDBDocComment docCom = finder.find(new NullProgressMonitor(), element);

		if(docCom == null) {
			log.debug(ILogLevel.LEVEL_MID,
				String.format("Did not find doc comment for(%s)", SVDBItem.getName(element)));
			return null;
		}
		
		return new SVNaturalDocHoverContentProvider(docCom);
	}
	
	private SVDeclarationInfoHoverContentProvider getDeclarationHoverContent(
			OpenDeclResult						target,
			IRegion								hoverRegion) {
		ISVDBItemBase element = target.getItem();
		
		if (!(element instanceof ISVDBNamedItem)) {
			return null;
		}
		
		if (SVDeclarationInfoHoverContentProvider.SUPPORTED_TYPES.contains(element.getType())) {
			return new SVDeclarationInfoHoverContentProvider();
		} else {
			return null;
		}
	}
	
	private SVMacroExpansionHoverContentProvider getMacroExpansionHoverContent(
			SVExprContext						ctxt,
			OpenDeclResult						target,
			IRegion								hoverRegion) {
		
		if (ctxt.fTrigger != null && ctxt.fTrigger.equals("`") &&
				ctxt.fLeaf != null && target.getItem() != null) {
			// Macro call
		}
		
		return null;
	}

}