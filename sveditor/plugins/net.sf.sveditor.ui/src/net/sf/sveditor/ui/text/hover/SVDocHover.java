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
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.docs.IDocTopicManager;
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

//	/**
//	 * Action to go back to the previous input in the hover control.
//	 *
//	 * @since 3.4
//	 */
//	private static final class BackAction extends Action {
//		private final BrowserInformationControl fInfoControl;
//
//		public BackAction(BrowserInformationControl infoControl) {
//			fInfoControl= infoControl;
//			setText(SVHoverMessages.JavadocHover_back);
//			ISharedImages images= PlatformUI.getWorkbench().getSharedImages();
//			setImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_TOOL_BACK));
//			setDisabledImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_TOOL_BACK_DISABLED));
//
//			update();
//		}
//
//		@Override
//		public void run() {
//			BrowserInformationControlInput previous= (BrowserInformationControlInput) fInfoControl.getInput().getPrevious();
//			if (previous != null) {
//				fInfoControl.setInput(previous);
//			}
//		}
//
//		public void update() {
//			BrowserInformationControlInput current= fInfoControl.getInput();
//
//			if (current != null && current.getPrevious() != null) {
//				BrowserInput previous= current.getPrevious();
//				setToolTipText(Messages.format(SVHoverMessages.JavadocHover_back_toElement_toolTip, BasicElementLabels.getJavaElementName(previous.getInputName())));
//				setEnabled(true);
//			} else {
//				setToolTipText(SVHoverMessages.JavadocHover_back);
//				setEnabled(false);
//			}
//		}
//	}

//	/**
//	 * Action to go forward to the next input in the hover control.
//	 *
//	 * @since 3.4
//	 */
//	private static final class ForwardAction extends Action {
//		private final BrowserInformationControl fInfoControl;
//
//		public ForwardAction(BrowserInformationControl infoControl) {
//			fInfoControl= infoControl;
//			setText(SVHoverMessages.JavadocHover_forward);
//			ISharedImages images= PlatformUI.getWorkbench().getSharedImages();
//			setImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_TOOL_FORWARD));
//			setDisabledImageDescriptor(images.getImageDescriptor(ISharedImages.IMG_TOOL_FORWARD_DISABLED));
//
//			update();
//		}
//
//		@Override
//		public void run() {
//			BrowserInformationControlInput next= (BrowserInformationControlInput) fInfoControl.getInput().getNext();
//			if (next != null) {
//				fInfoControl.setInput(next);
//			}
//		}
//
//		public void update() {
//			BrowserInformationControlInput current= fInfoControl.getInput();
//
//			if (current != null && current.getNext() != null) {
//				setToolTipText(Messages.format(SVHoverMessages.JavadocHover_forward_toElement_toolTip, BasicElementLabels.getJavaElementName(current.getNext().getInputName())));
//				setEnabled(true);
//			} else {
//				setToolTipText(SVHoverMessages.JavadocHover_forward_toolTip);
//				setEnabled(false);
//			}
//		}
//	}

//	/**
//	 * Action that shows the current hover contents in the Javadoc view.
//	 *
//	 * @since 3.4
//	 */
//	private static final class ShowInJavadocViewAction extends Action {
//		private final BrowserInformationControl fInfoControl;
//
//		public ShowInJavadocViewAction(BrowserInformationControl infoControl) {
//			fInfoControl= infoControl;
//			setText(SVHoverMessages.JavadocHover_showInJavadoc);
//			setImageDescriptor(JavaPluginImages.DESC_OBJS_JAVADOCTAG); //TODO: better image
//		}
//
//		/*
//		 * @see org.eclipse.jface.action.Action#run()
//		 */
//		@Override
//		public void run() {
//			JavadocBrowserInformationControlInput infoInput= (JavadocBrowserInformationControlInput) fInfoControl.getInput(); //TODO: check cast
//			fInfoControl.notifyDelayedInputChange(null);
//			fInfoControl.dispose(); //FIXME: should have protocol to hide, rather than dispose
//			try {
//				JavadocView view= (JavadocView) JavaPlugin.getActivePage().showView(JavaUI.ID_JAVADOC_VIEW);
//				view.setInput(infoInput);
//			} catch (PartInitException e) {
//				JavaPlugin.log(e);
//			}
//		}
//	}

//	/**
//	 * Action that opens the current hover input element.
//	 *
//	 * @since 3.4
//	 */
//	private static final class OpenDeclarationAction extends Action {
//		private final BrowserInformationControl fInfoControl;
//
//		public OpenDeclarationAction(BrowserInformationControl infoControl) {
//			fInfoControl= infoControl;
//			setText(SVHoverMessages.JavadocHover_openDeclaration);
//			JavaPluginImages.setLocalImageDescriptors(this, "goto_input.gif"); //$NON-NLS-1$ //TODO: better images
//		}
//
//		/*
//		 * @see org.eclipse.jface.action.Action#run()
//		 */
//		@Override
//		public void run() {
//			JavadocBrowserInformationControlInput infoInput= (JavadocBrowserInformationControlInput) fInfoControl.getInput(); //TODO: check cast
//			fInfoControl.notifyDelayedInputChange(null);
//			fInfoControl.dispose(); //FIXME: should have protocol to hide, rather than dispose
//
//			try {
//				//FIXME: add hover location to editor navigation history?
//				JavaUI.openInEditor(infoInput.getElement());
//			} catch (PartInitException e) {
//				JavaPlugin.log(e);
//			} catch (JavaModelException e) {
//				JavaPlugin.log(e);
//			}
//		}
//	}


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
//				String font= PreferenceConstants.APPEARANCE_JAVADOC_FONT;
//				BrowserInformationControl iControl= new BrowserInformationControl(parent, font, tbm);
				BrowserInformationControl iControl= new BrowserInformationControl(parent, JFaceResources.getTextFont().toString(), tbm);

//				final BackAction backAction= new BackAction(iControl);
//				backAction.setEnabled(false);
//				tbm.add(backAction);
//				final ForwardAction forwardAction= new ForwardAction(iControl);
//				tbm.add(forwardAction);
//				forwardAction.setEnabled(false);
//
//				final ShowInJavadocViewAction showInJavadocViewAction= new ShowInJavadocViewAction(iControl);
//				tbm.add(showInJavadocViewAction);
//				final OpenDeclarationAction openDeclarationAction= new OpenDeclarationAction(iControl);
//				tbm.add(openDeclarationAction);

//				final SimpleSelectionProvider selectionProvider= new SimpleSelectionProvider();
//				if (fSite != null) {
//					OpenAttachedJavadocAction openAttachedJavadocAction= new OpenAttachedJavadocAction(fSite);
//					openAttachedJavadocAction.setSpecialSelectionProvider(selectionProvider);
//					openAttachedJavadocAction.setImageDescriptor(JavaPluginImages.DESC_ELCL_OPEN_BROWSER);
//					openAttachedJavadocAction.setDisabledImageDescriptor(JavaPluginImages.DESC_DLCL_OPEN_BROWSER);
//					selectionProvider.addSelectionChangedListener(openAttachedJavadocAction);
//					selectionProvider.setSelection(new StructuredSelection());
//					tbm.add(openAttachedJavadocAction);
//				}

//				IInputChangedListener inputChangeListener= new IInputChangedListener() {
//					public void inputChanged(Object newInput) {
//						backAction.update();
//						forwardAction.update();
//						if (newInput == null) {
//							selectionProvider.setSelection(new StructuredSelection());
//						} else if (newInput instanceof BrowserInformationControlInput) {
//							BrowserInformationControlInput input= (BrowserInformationControlInput) newInput;
//							Object inputElement= input.getInputElement();
//							selectionProvider.setSelection(new StructuredSelection(inputElement));
//							boolean isJavaElementInput= inputElement instanceof IJavaElement;
//							showInJavadocViewAction.setEnabled(isJavaElementInput);
//							openDeclarationAction.setEnabled(isJavaElementInput);
//						}
//					}
//				};
//				iControl.addInputChangeListener(inputChangeListener);

				tbm.update(true);

//				addLinkListener(iControl);
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
//			String tooltipAffordanceString= fAdditionalInfoAffordance ? JavaPlugin.getAdditionalInfoAffordanceString() : EditorsUI.getTooltipAffordanceString();
			Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
			Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));
			if (BrowserInformationControl.isAvailable(parent) &&
					prefs.getBoolean(SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_USES_BROWSER)) {
//				String font= PreferenceConstants.APPEARANCE_JAVADOC_FONT;
//				BrowserInformationControl iControl= new BrowserInformationControl(parent, font, tooltipAffordanceString) {
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
//				addLinkListener(iControl);
				return iControl;
			} else {
//				return new DefaultInformationControl(parent, tooltipAffordanceString);
				DefaultInformationControl hover = new SVDefaultInformationControl(
						parent, "todo", bg_color, fg_color);
				return hover;
			}
		}
		
		private final class SVDefaultInformationControl extends DefaultInformationControl 
			implements IInformationControlCreator {
			IInformationControlCreator		fCreator;
			Color							fBgColor;
			Color							fFgColor;
			
			public SVDefaultInformationControl(
					Shell parent, 
					String msg,
					Color			bg_color,
					Color			fg_color) {
				super(parent, msg);
				setBackgroundColor(bg_color);
				setForegroundColor(fg_color);
				fBgColor = bg_color;
				fFgColor = fg_color;
			}

			@Override
			public IInformationControlCreator getInformationPresenterControlCreator() {
				fCreator = super.getInformationPresenterControlCreator();
				return this;
			}

			@Override
			public IInformationControl createInformationControl(Shell parent) {
				IInformationControl c = fCreator.createInformationControl(parent);
				if (c instanceof DefaultInformationControl) {
					((DefaultInformationControl)c).setBackgroundColor(fBgColor);
					((DefaultInformationControl)c).setForegroundColor(fFgColor);
				}
				return c;
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

//	private static final long LABEL_FLAGS=  JavaElementLabels.ALL_FULLY_QUALIFIED
//		| JavaElementLabels.M_PRE_RETURNTYPE | JavaElementLabels.M_PARAMETER_ANNOTATIONS | JavaElementLabels.M_PARAMETER_TYPES | JavaElementLabels.M_PARAMETER_NAMES | JavaElementLabels.M_EXCEPTIONS
//		| JavaElementLabels.F_PRE_TYPE_SIGNATURE | JavaElementLabels.M_PRE_TYPE_PARAMETERS | JavaElementLabels.T_TYPE_PARAMETERS
//		| JavaElementLabels.USE_RESOLVED;
//	private static final long LOCAL_VARIABLE_FLAGS= LABEL_FLAGS & ~JavaElementLabels.F_FULLY_QUALIFIED | JavaElementLabels.F_POST_QUALIFIED;
//	private static final long TYPE_PARAMETER_FLAGS= LABEL_FLAGS | JavaElementLabels.TP_POST_QUALIFIED;

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

//	private static void addLinkListener(final BrowserInformationControl control) {
//		control.addLocationListener(JavaElementLinks.createLocationListener(new JavaElementLinks.ILinkHandler() {
//			/* (non-Javadoc)
//			 * @see org.eclipse.jdt.internal.ui.viewsupport.JavaElementLinks.ILinkHandler#handleJavadocViewLink(org.eclipse.jdt.core.IJavaElement)
//			 */
//			public void handleJavadocViewLink(IJavaElement linkTarget) {
//				control.notifyDelayedInputChange(null);
//				control.setVisible(false);
//				control.dispose(); //FIXME: should have protocol to hide, rather than dispose
//				try {
//					JavadocView view= (JavadocView) JavaPlugin.getActivePage().showView(JavaUI.ID_JAVADOC_VIEW);
//					view.setInput(linkTarget);
//				} catch (PartInitException e) {
//					JavaPlugin.log(e);
//				}
//			}
//
//			/* (non-Javadoc)
//			 * @see org.eclipse.jdt.internal.ui.viewsupport.JavaElementLinks.ILinkHandler#handleInlineJavadocLink(org.eclipse.jdt.core.IJavaElement)
//			 */
//			public void handleInlineJavadocLink(IJavaElement linkTarget) {
//				JavadocBrowserInformationControlInput hoverInfo= getHoverInfo(new IJavaElement[] { linkTarget }, null, null, (JavadocBrowserInformationControlInput) control.getInput());
//				if (control.hasDelayedInputChangeListener())
//					control.notifyDelayedInputChange(hoverInfo);
//				else
//					control.setInput(hoverInfo);
//			}
//
//			/* (non-Javadoc)
//			 * @see org.eclipse.jdt.internal.ui.viewsupport.JavaElementLinks.ILinkHandler#handleDeclarationLink(org.eclipse.jdt.core.IJavaElement)
//			 */
//			public void handleDeclarationLink(IJavaElement linkTarget) {
//				control.notifyDelayedInputChange(null);
//				control.dispose(); //FIXME: should have protocol to hide, rather than dispose
//				try {
//					//FIXME: add hover location to editor navigation history?
//					JavaUI.openInEditor(linkTarget);
//				} catch (PartInitException e) {
//					JavaPlugin.log(e);
//				} catch (JavaModelException e) {
//					JavaPlugin.log(e);
//				}
//			}
//
//			/* (non-Javadoc)
//			 * @see org.eclipse.jdt.internal.ui.viewsupport.JavaElementLinks.ILinkHandler#handleExternalLink(java.net.URL, org.eclipse.swt.widgets.Display)
//			 */
//			public boolean handleExternalLink(URL url, Display display) {
//				control.notifyDelayedInputChange(null);
//				control.dispose(); //FIXME: should have protocol to hide, rather than dispose
//
//				// Open attached Javadoc links
//				OpenBrowserUtil.open(url, display);
//
//				return true;
//			}
//
//			public void handleTextSet() {
//			}
//		}));
//	}

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
		for(DocTopic topic: topics) {
			res += genContentForTopic(topic) ;
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
	private SVDocBrowserInformationControlInput getHoverInfo(Tuple<ISVDBItemBase, SVDBFile> target, IRegion hoverRegion, SVDocBrowserInformationControlInput previousInput) {
		
		StringBuffer buffer= new StringBuffer();
		boolean hasContents= false;
		
		ISVDBItemBase element = target.first() ;
		
		if(!(element instanceof ISVDBNamedItem )) {
			return null ;
		}
		
		ISVDBNamedItem namedItem = (ISVDBNamedItem)element ;

		hasContents = true ; // FIXME: temp
		
		ISVDBItemBase p = element ;
		while (p != null && p.getType() != SVDBItemType.File) {
			if (p instanceof ISVDBChildItem) {
				p = ((ISVDBChildItem)p).getParent();
			} else {
				p = null;
				break ;
			}
		}		
		
		if(p == null) {
			log.error(String.format("Failed to find file for type(%s)",namedItem.getName())) ;
			return null ;
		}

		// TODO: should be looking at the live view of the editor
		ISVDBIndex index = ((SVEditor)getEditor()).getSVDBIndex();
		SVDBFile ppFile = index.findPreProcFile(((SVDBFile)p).getFilePath());
		
		SVDBDocComment docCom = null ;
	
		if (ppFile != null) {
			for(ISVDBChildItem child: ppFile.getChildren()) {
				if(child instanceof SVDBDocComment) {
					SVDBDocComment tryDocCom = (SVDBDocComment)child ;
					if(tryDocCom.getName().equals(namedItem.getName())) {
						log.debug(ILogLevel.LEVEL_MID,
								String.format("Found doc comment for(%s)",namedItem.getName())) ;
						docCom = tryDocCom ;
						break ;
					}
				}
			}
		} else {
			log.debug(ILogLevel.LEVEL_MID, "Failed to find pre-proc file " + 
					((SVDBFile)p).getFilePath());
		}
		
		if(docCom == null) {
			log.debug(ILogLevel.LEVEL_MID,
				String.format("Did not find doc comment for(%s)",namedItem.getName())) ;
			return null ;
		}
		
		List<DocTopic> docTopics = new ArrayList<DocTopic>() ;
		
		IDocTopicManager topicMgr = new DocTopicManager() ;
		
		IDocCommentParser docCommentParser = new DocCommentParser(topicMgr) ;
			
		docCommentParser.parse(docCom.getRawComment(), docTopics) ;
		
		buffer.append(genContent(docTopics)) ;

//		if (nResults > 1) {
//
//			for (int i= 0; i < elements.length; i++) {
//				HTMLPrinter.startBulletList(buffer);
//				IJavaElement curr= elements[i];
//				if (curr instanceof IMember || curr.getElementType() == IJavaElement.LOCAL_VARIABLE) {
//					String label= JavaElementLabels.getElementLabel(curr, getHeaderFlags(curr));
//					String link;
//					try {
//						String uri= JavaElementLinks.createURI(JavaElementLinks.JAVADOC_SCHEME, curr);
//						link= JavaElementLinks.createLink(uri, label);
//					} catch (URISyntaxException e) {
//						JavaPlugin.log(e);
//						link= label;
//					}
//					HTMLPrinter.addBullet(buffer, link);
//					hasContents= true;
//				}
//				HTMLPrinter.endBulletList(buffer);
//			}
//
//		} else {
//
//			element= elements[0];
//			if (element instanceof IMember) {
//				HTMLPrinter.addSmallHeader(buffer, getInfoText(element, editorInputElement, hoverRegion, true));
//				buffer.append("<br>"); //$NON-NLS-1$
//				addAnnotations(buffer, element, editorInputElement, hoverRegion);
//				IMember member= (IMember) element;
//				Reader reader;
//				try {
////					reader= JavadocContentAccess.getHTMLContentReader(member, true, true);
//					String content= JavadocContentAccess2.getHTMLContent(member, true);
//					reader= content == null ? null : new StringReader(content);
//
//					// Provide hint why there's no Javadoc
//					if (reader == null && member.isBinary()) {
//						boolean hasAttachedJavadoc= JavaDocLocations.getJavadocBaseLocation(member) != null;
//						IPackageFragmentRoot root= (IPackageFragmentRoot)member.getAncestor(IJavaElement.PACKAGE_FRAGMENT_ROOT);
//						boolean hasAttachedSource= root != null && root.getSourceAttachmentPath() != null;
//						IOpenable openable= member.getOpenable();
//						boolean hasSource= openable.getBuffer() != null;
//
//						if (!hasAttachedSource && !hasAttachedJavadoc)
//							reader= new StringReader(SVHoverMessages.JavadocHover_noAttachments);
//						else if (!hasAttachedJavadoc && !hasSource)
//							reader= new StringReader(SVHoverMessages.JavadocHover_noAttachedJavadoc);
//						else if (!hasAttachedSource)
//							reader= new StringReader(SVHoverMessages.JavadocHover_noAttachedSource);
//						else if (!hasSource)
//							reader= new StringReader(SVHoverMessages.JavadocHover_noInformation);
//
//					} else {
//						base= JavaDocLocations.getBaseURL(member);
//					}
//
//				} catch (JavaModelException ex) {
//					reader= new StringReader(SVHoverMessages.JavadocHover_error_gettingJavadoc);
//					JavaPlugin.log(ex);
//				}
//
//				if (reader != null) {
//					HTMLPrinter.addParagraph(buffer, reader);
//				}
//				hasContents= true;
//
//			} else if (element.getElementType() == IJavaElement.LOCAL_VARIABLE || element.getElementType() == IJavaElement.TYPE_PARAMETER) {
//				addAnnotations(buffer, element, editorInputElement, hoverRegion);
//				HTMLPrinter.addSmallHeader(buffer, getInfoText(element, editorInputElement, hoverRegion, true));
//				hasContents= true;
//			}
//			leadingImageWidth= 20;
//		}

		if (!hasContents)
			return null;
		
		if (buffer.length() > 0) {
			HTMLPrinter.insertPageProlog(buffer, 0, getStyleSheet());
//			HTMLPrinter.insertPageProlog(buffer, 0) ;
//			if (base != null) {
//				int endHeadIdx= buffer.indexOf("</head>"); //$NON-NLS-1$
//				buffer.insert(endHeadIdx, "\n<base href='" + base + "'>\n"); //$NON-NLS-1$ //$NON-NLS-2$
//			}
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
			items = OpenDeclUtils.openDecl(
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
//		if (css != null) {
//			FontData fontData= JFaceResources.getFontRegistry().getFontData(PreferenceConstants.APPEARANCE_JAVADOC_FONT)[0];
//			css= HTMLPrinter.convertTopLevelFont(css, fontData);
//		}

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

//	public static void addImageAndLabel(StringBuffer buf, IJavaElement element, String imageSrcPath, int imageWidth, int imageHeight, String label, int labelLeft, int labelTop) {
//		buf.append("<div style='word-wrap: break-word; position: relative; "); //$NON-NLS-1$
//		
//		if (imageSrcPath != null) {
//			buf.append("margin-left: ").append(labelLeft).append("px; "); //$NON-NLS-1$ //$NON-NLS-2$
//			buf.append("padding-top: ").append(labelTop).append("px; "); //$NON-NLS-1$ //$NON-NLS-2$
//		}
//
//		buf.append("'>"); //$NON-NLS-1$
//		if (imageSrcPath != null) {
//			if (element != null) {
//				try {
//					String uri= JavaElementLinks.createURI(JavaElementLinks.OPEN_LINK_SCHEME, element);
//					buf.append("<a href='").append(uri).append("'>");  //$NON-NLS-1$//$NON-NLS-2$
//				} catch (URISyntaxException e) {
//					element= null; // no link
//				}
//			}
//			StringBuffer imageStyle= new StringBuffer("border:none; position: absolute; "); //$NON-NLS-1$
//			imageStyle.append("width: ").append(imageWidth).append("px; "); //$NON-NLS-1$ //$NON-NLS-2$
//			imageStyle.append("height: ").append(imageHeight).append("px; "); //$NON-NLS-1$ //$NON-NLS-2$
//			imageStyle.append("left: ").append(- labelLeft - 1).append("px; "); //$NON-NLS-1$ //$NON-NLS-2$
//
//			// hack for broken transparent PNG support in IE 6, see https://bugs.eclipse.org/bugs/show_bug.cgi?id=223900 :
//			buf.append("<!--[if lte IE 6]><![if gte IE 5.5]>\n"); //$NON-NLS-1$
//			String tooltip= element == null ? "" : "alt='" + SVHoverMessages.JavadocHover_openDeclaration + "' "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
//			buf.append("<span ").append(tooltip).append("style=\"").append(imageStyle). //$NON-NLS-1$ //$NON-NLS-2$
//					append("filter:progid:DXImageTransform.Microsoft.AlphaImageLoader(src='").append(imageSrcPath).append("')\"></span>\n"); //$NON-NLS-1$ //$NON-NLS-2$
//			buf.append("<![endif]><![endif]-->\n"); //$NON-NLS-1$
//
//			buf.append("<!--[if !IE]>-->\n"); //$NON-NLS-1$
//			buf.append("<img ").append(tooltip).append("style='").append(imageStyle).append("' src='").append(imageSrcPath).append("'/>\n"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
//			buf.append("<!--<![endif]-->\n"); //$NON-NLS-1$
//			buf.append("<!--[if gte IE 7]>\n"); //$NON-NLS-1$
//			buf.append("<img ").append(tooltip).append("style='").append(imageStyle).append("' src='").append(imageSrcPath).append("'/>\n"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
//			buf.append("<![endif]-->\n"); //$NON-NLS-1$
//			if (element != null) {
//				buf.append("</a>"); //$NON-NLS-1$
//			}
//		}
//		
//		buf.append(label);
//		
//		buf.append("</div>"); //$NON-NLS-1$
//	}




//
//	private static StringBuffer addLink(StringBuffer buf, String uri, String label) {
//		return buf.append(JavaElementLinks.createLink(uri, label));
//	}
		

		
}