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
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVColorManager;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.jface.internal.text.html.BrowserInformationControl;
import org.eclipse.jface.internal.text.html.HTMLPrinter;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.AbstractReusableInformationControlCreator;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IInformationControlExtension4;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchSite;
import org.osgi.framework.Bundle;


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
	 * Presenter control creator.
	 *
	 * @since 3.3
	 */
	public static final class PresenterControlCreator extends AbstractReusableInformationControlCreator {

		private IWorkbenchSite fSite;

		/**
		 * Creates a new PresenterControlCreator.
		 * 
		 * @param site the site or <code>null</code> if none
		 * @since 3.6
		 */
		public PresenterControlCreator(IWorkbenchSite site) {
			fSite= site;
		}

		/*
		 * @see org.eclipse.jdt.internal.ui.text.java.hover.AbstractReusableInformationControlCreator#doCreateInformationControl(org.eclipse.swt.widgets.Shell)
		 */
		@Override
		public IInformationControl doCreateInformationControl(Shell parent) {
			IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
			
			// Use the browser widget if available and the user enables it
			if (BrowserInformationControl.isAvailable(parent) &&
					prefs.getBoolean(SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_USES_BROWSER)) {
				ToolBarManager tbm= new ToolBarManager(SWT.FLAT);

				BrowserInformationControl iControl= new BrowserInformationControl(parent, JFaceResources.getTextFont().toString(), tbm);


				tbm.update(true);

				return iControl;

			} else {
				return new DefaultInformationControl(parent, true);
			}
		}
	}


	/**
	 * Hover control creator.
	 *
	 */
	public static final class HoverControlCreator extends AbstractReusableInformationControlCreator {
		/**
		 * The information presenter control creator.
		 */
		private final IInformationControlCreator fInformationPresenterControlCreator;
		/**
		 * <code>true</code> to use the additional info affordance, <code>false</code> to use the hover affordance.
		 */
		private final boolean fAdditionalInfoAffordance;

		/**
		 * @param informationPresenterControlCreator control creator for enriched hover
		 */
		public HoverControlCreator(IInformationControlCreator informationPresenterControlCreator) {
			this(informationPresenterControlCreator, false);
		}

		/**
		 * @param informationPresenterControlCreator control creator for enriched hover
		 * @param additionalInfoAffordance <code>true</code> to use the additional info affordance, <code>false</code> to use the hover affordance
		 */
		public HoverControlCreator(IInformationControlCreator informationPresenterControlCreator, boolean additionalInfoAffordance) {
			fInformationPresenterControlCreator= informationPresenterControlCreator;
			fAdditionalInfoAffordance= additionalInfoAffordance;
		}

		/*
		 * @see org.eclipse.jdt.internal.ui.text.java.hover.AbstractReusableInformationControlCreator#doCreateInformationControl(org.eclipse.swt.widgets.Shell)
		 */
		@Override
		public IInformationControl doCreateInformationControl(Shell parent) {
			IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
			Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
			Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));
			if (BrowserInformationControl.isAvailable(parent) &&
					prefs.getBoolean(SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_USES_BROWSER)) {
				BrowserInformationControl iControl= new BrowserInformationControl(parent, "", "todo") {
					/*
					 * @see org.eclipse.jface.text.IInformationControlExtension5#getInformationPresenterControlCreator()
					 */
					@Override
					public IInformationControlCreator getInformationPresenterControlCreator() {
						return fInformationPresenterControlCreator;
					}
				};
				iControl.setBackgroundColor(bg_color);
				iControl.setForegroundColor(fg_color);
				return iControl;
			} else {
				DefaultInformationControl hover = new SVDefaultInformationControl(
						parent, "todo", bg_color, fg_color);
				return hover;
			}
		}
		
		/*
		 * @see org.eclipse.jdt.internal.ui.text.java.hover.AbstractReusableInformationControlCreator#canReuse(org.eclipse.jface.text.IInformationControl)
		 */
		@Override
		public boolean canReuse(IInformationControl control) {
			if (!super.canReuse(control))
				return false;

			if (control instanceof IInformationControlExtension4) {
//				String tooltipAffordanceString= fAdditionalInfoAffordance ? JavaPlugin.getAdditionalInfoAffordanceString() : EditorsUI.getTooltipAffordanceString();
				String tooltipAffordanceString= "todo" ;
				((IInformationControlExtension4)control).setStatusText(tooltipAffordanceString);
			}

			return true;
		}
	}

	/**
	 * The style sheet (css).
	 */
	private static String fgStyleSheet;

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

	/*
	 * @see org.eclipse.jdt.internal.ui.text.java.hover.AbstractJavaEditorTextHover#getInformationPresenterControlCreator()
	 * @since 3.1
	 */
	@Override
	public IInformationControlCreator getInformationPresenterControlCreator() {
		if (fPresenterControlCreator == null)
			fPresenterControlCreator= new PresenterControlCreator(getSite());
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
		if (fHoverControlCreator == null)
			fHoverControlCreator= new HoverControlCreator(getInformationPresenterControlCreator());
		return fHoverControlCreator;
	}

	/**
	 * @deprecated see {@link org.eclipse.jface.text.ITextHover#getHoverInfo(ITextViewer, IRegion)}
	 */
	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		SVDocBrowserInformationControlInput info= (SVDocBrowserInformationControlInput) getHoverInfo2(textViewer, hoverRegion);
		return info != null ? info.getHtml() : null;
	}

	/*
	 * @see org.eclipse.jface.text.ITextHoverExtension2#getHoverInfo2(org.eclipse.jface.text.ITextViewer, org.eclipse.jface.text.IRegion)
	 */
	@Override
	public Object getHoverInfo2(ITextViewer textViewer, IRegion hoverRegion) {
		return internalGetHoverInfo(textViewer, hoverRegion);
	}

	private SVDocBrowserInformationControlInput internalGetHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		
		Tuple<ISVDBItemBase, SVDBFile>  target = findTarget(hoverRegion) ;
		
		if(target == null)
			return null ;

		return getHoverInfo(target, hoverRegion, null);
		
	}
	
	private String genContent(List<DocTopic> topics) {
		String res = "" ;
		HTMLFromNDMarkup markupConverter = new HTMLFromNDMarkup() ;
		for(DocTopic topic: topics) {
			String html = "" ;
			html = genContentForTopic(topic) ;
			html = markupConverter.convertNDMarkupToHTML(null, topic, html, HTMLFromNDMarkup.NDMarkupToHTMLStyle.Tooltip) ;
			res += html ;
		}
		return res ;
	}		
	
	private String genContentForTopic(DocTopic topic) {
		String res = "" ;
		res += "<h4>" ;
		res += topic.getTitle() ;
		res += "</h4>" ;
		res += topic.getBody() ;
		for(DocTopic childTopic: topic.getChildren()) {
			res += genContentForTopic(childTopic) ;
		}
		return res ;
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
	private SVDocBrowserInformationControlInput getHoverInfo(
			Tuple<ISVDBItemBase, SVDBFile> 		target, 
			IRegion 							hoverRegion, 
			SVDocBrowserInformationControlInput previousInput) {
		
		StringBuffer buffer= new StringBuffer();
		
		ISVDBItemBase element = target.first() ;
		
		if(!(element instanceof ISVDBNamedItem )) {
			return null ;
		}
		
		ISVDBIndexIterator index_it = ((SVEditor)getEditor()).getSVDBIndex();
		
		// Find the doc comment corresponding to the specified element
		SVDBFindDocComment finder = new SVDBFindDocComment(index_it);
		SVDBDocComment docCom = finder.find(new NullProgressMonitor(), element);

		if(docCom == null) {
			log.debug(ILogLevel.LEVEL_MID,
				String.format("Did not find doc comment for(%s)", SVDBItem.getName(element)));
			return null ;
		}
		
		List<DocTopic> docTopics = new ArrayList<DocTopic>() ;
		
		IDocTopicManager topicMgr = new DocTopicManager() ;
		
		IDocCommentParser docCommentParser = new DocCommentParser(topicMgr) ;
		
		log.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;
		log.debug(ILogLevel.LEVEL_MID, 
				"| Raw Comment") ;
		log.debug(ILogLevel.LEVEL_MID,
				"| " + docCom.getRawComment()) ;
		log.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;
			
		docCommentParser.parse(docCom.getRawComment(), docTopics) ;
		
		buffer.append(genContent(docTopics)) ;

		if (buffer.length() > 0) {
			HTMLPrinter.insertPageProlog(buffer, 0, getStyleSheet());
			HTMLPrinter.addPageEpilog(buffer);
			
			log.debug(ILogLevel.LEVEL_MID, 
					"+------------------------------------------------------------------") ;
			log.debug(ILogLevel.LEVEL_MID, 
					"| HTML dump") ;
			log.debug(ILogLevel.LEVEL_MID,
					buffer.toString()) ;
			log.debug(ILogLevel.LEVEL_MID, 
					"+------------------------------------------------------------------") ;
			log.debug(ILogLevel.LEVEL_MID, 
					"+------------------------------------------------------------------") ;

			return new SVDocBrowserInformationControlInput(previousInput, target, buffer.toString(), 0);
		}

		return null;
	}

	
	protected Tuple<ISVDBItemBase, SVDBFile> findTarget(IRegion hoverRegion) {
		SVEditor editor = ((SVEditor)getEditor()) ;
		IDocument doc = editor.getDocument() ;
		
		int offset = hoverRegion.getOffset() ;
		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		scanner.setSkipComments(true) ;
		
		List<Tuple<ISVDBItemBase, SVDBFile>> items = null ;
		
		try {
			items = OpenDeclUtils.openDecl_2(
					editor.getSVDBFile(),
					doc.getLineOfOffset(hoverRegion.getOffset()),
					scanner,
					editor.getIndexIterator());
		} catch (BadLocationException e) {
			log.error("Received bogus hover region", e) ;
		}

		if (items != null && items.size() > 0) {
			return items.get(0);
		} else {
			return new Tuple<ISVDBItemBase, SVDBFile>(null, null);
		}
	}	



	/**
	 * Returns the SVDoc hover style sheet 
	 * @return the updated style sheet
	 */
	private String getStyleSheet() {
		if (fgStyleSheet == null)
			fgStyleSheet= loadStyleSheet();
		String css= fgStyleSheet;
		return css;
	}

	/**
	 * Loads and returns the SVDoc hover style sheet.
	 * @return the style sheet, or <code>null</code> if unable to load
	 */
	private String loadStyleSheet() {
		Bundle bundle= Platform.getBundle(SVUiPlugin.PLUGIN_ID) ;
		URL styleSheetURL= bundle.getEntry("/SVDocHoverStyleSheet.css"); //$NON-NLS-1$
		if (styleSheetURL != null) {
			BufferedReader reader= null;
			try {
				reader= new BufferedReader(new InputStreamReader(styleSheetURL.openStream()));
				StringBuffer buffer= new StringBuffer(1500);
				String line= reader.readLine();
				while (line != null) {
					buffer.append(line);
					buffer.append('\n');
					line= reader.readLine();
				}
				return buffer.toString();
			} catch (IOException ex) {
				log.error("Exception while loading style sheet", ex) ;
				return ""; //$NON-NLS-1$
			} finally {
				try {
					if (reader != null)
						reader.close();
				} catch (IOException e) {
				}
			}
		}
		return null;
	}

}