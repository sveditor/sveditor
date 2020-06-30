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
 *     Genady Beryozkin <eclipse@genady.org> - [hovering] tooltip for constant string does not show constant value - https://bugs.eclipse.org/bugs/show_bug.cgi?id=85382
 *     Armond Paiva - repurposed from JDT for use in sveditor
 *******************************************************************************/

package net.sf.sveditor.ui.text.hover;

import java.util.List;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBDocComment;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBMacroDef;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindDocComment;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprContext;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclUtils;
import org.eclipse.hdt.sveditor.core.preproc.ISVStringPreProcessor;
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
		List<Tuple<ISVDBItemBase, SVDBFile>> items = null;
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
		
		ISVStringPreProcessor preproc = editor.createPreProcessor(line);
	
		items = OpenDeclUtils.openDecl_2(
				file, 
				line, 
				scanner, 
				preproc, 
				editor.getIndexIterator());
		
		Tuple<SVExprContext, ISVDBScopeItem> context_scope = OpenDeclUtils.getContextScope(
				file, line, scanner);
		SVExprContext ctxt = context_scope.first();
//		
//		
//		items = OpenDeclUtils.openDecl(context_scope.first(), 
//				context_scope.second(), editor.getIndexIterator());
		
		if (items == null || items.size() == 0) {
			return null;
		}
	
		Tuple<ISVDBItemBase, SVDBFile> result = items.get(0);
		
		ret = new SVHoverInformationControlInput(
				result.first(),
				context_scope.second(), // active scope
				editor.getIndexIterator());
		SVHoverContentProvider cp = null;
		
		if ((cp = getNaturalDocHoverContent(result, hoverRegion)) != null) {
			ret.setContentProvider(SVHoverInformationControlInput.CONTENT_DOC, cp);
		}
		
		if ((cp = getDeclarationHoverContent(result, hoverRegion)) != null) {
			ret.setContentProvider(SVHoverInformationControlInput.CONTENT_DECL, cp);
		}
		
		if ((cp = getMacroExpansionHoverContent(ctxt, line, result)) != null) {
			ret.setContentProvider(SVHoverInformationControlInput.CONTENT_MACRO_EXP, cp);
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
			Tuple<ISVDBItemBase, SVDBFile>		target,
			IRegion 							hoverRegion) {
		ISVDBItemBase element = target.first();
		
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
			Tuple<ISVDBItemBase, SVDBFile>		target,
			IRegion								hoverRegion) {
		ISVDBItemBase element = target.first();
		
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
			int									lineno,
			Tuple<ISVDBItemBase, SVDBFile>		target) {
		
		if (ctxt.fTrigger != null && ctxt.fTrigger.equals("`") &&
				ctxt.fLeaf != null && target.first() != null && 
				target.first().getType() == SVDBItemType.MacroDef) {
			SVEditor editor = ((SVEditor)getEditor()) ;
			IDocument doc = editor.getDocument() ;

//			int offset = hoverRegion.getOffset() ;
			SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, ctxt.fStart);
			scanner.setSkipComments(true);
			scanner.setScanFwd(false);
	
			// Back up to get the trigger (`) char
			scanner.get_ch();
			
			scanner.setScanFwd(true);
			
			// Macro call
			SVDBMacroDef m = (SVDBMacroDef)target.first();
			
			String macro_call = OpenDeclUtils.extractMacroCall(scanner, 
					(m.getParameters() != null && m.getParameters().size() > 0));
			
			if (macro_call != null) {
				return new SVMacroExpansionHoverContentProvider(
						editor, macro_call, lineno);
			}
		}
		
		return null;
	}

}