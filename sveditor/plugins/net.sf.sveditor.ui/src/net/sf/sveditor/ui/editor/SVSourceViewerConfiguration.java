/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/



package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.text.HierarchyInformationControl;
import net.sf.sveditor.ui.text.ObjectsInformationControl;
import net.sf.sveditor.ui.text.OutlineInformationControl;
import net.sf.sveditor.ui.text.SVEditorProvider;
import net.sf.sveditor.ui.text.SVElementProvider;
import net.sf.sveditor.ui.text.hover.ISVEditorTextHover;
import net.sf.sveditor.ui.text.hover.SVDocHover;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.text.AbstractInformationControlManager;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.information.IInformationPresenter;
import org.eclipse.jface.text.information.IInformationProvider;
import org.eclipse.jface.text.information.InformationPresenter;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.reconciler.MonoReconciler;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.DefaultAnnotationHover;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditorPreferenceConstants;

public class SVSourceViewerConfiguration extends SourceViewerConfiguration {
	private SVEditor				fEditor;
	private ContentAssistant		fContentAssist;
	
	public SVSourceViewerConfiguration(SVEditor editor) {
		fEditor = editor;
	}
	
	@Override
	public String[] getIndentPrefixes(ISourceViewer sourceViewer,
			String contentType) {
		String prefix = SVUiPlugin.getDefault().getIndentIncr();
		return new String[] {prefix, "\t", ""};
	}

	@Override
	public int getTabWidth(ISourceViewer sourceViewer) {
		IPreferenceStore chainedPrefs = SVUiPlugin.getDefault().getChainedPrefs();
		/* boolean spaces_for_tabs = */ chainedPrefs.getBoolean(
				AbstractDecoratedTextEditorPreferenceConstants.EDITOR_SPACES_FOR_TABS);
		int tab_width = chainedPrefs.getInt(
				AbstractDecoratedTextEditorPreferenceConstants.EDITOR_TAB_WIDTH);

		return tab_width;
	}



	@Override
	public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
		if (fContentAssist == null) {
			fContentAssist = new ContentAssistant();
			IContentAssistProcessor p = new SVTemplateCompletionProcessor(fEditor);

			fContentAssist.setContentAssistProcessor(p,
					IDocument.DEFAULT_CONTENT_TYPE);
			fContentAssist.setInformationControlCreator(
					getInformationControlCreator(sourceViewer));
			fContentAssist.enableAutoActivation(true);
			fContentAssist.enableAutoInsert(true);
			fContentAssist.enablePrefixCompletion(true);
			/*
			fContentAssist.setAutoActivationDelay(100);
			 */
		}
		
		return fContentAssist;
	}
	
	@Override
	public IAutoEditStrategy[] getAutoEditStrategies(
			ISourceViewer sourceViewer, String contentType) {
        String partitioning = 
            getConfiguredDocumentPartitioning(sourceViewer);
        
        if (contentType.equals(SVDocumentPartitions.SV_MULTILINE_COMMENT)) {
        	return new IAutoEditStrategy[] {
        			new SVMultiLineCommentAutoIndentStrategy(partitioning)
        	};
        } else {
        	List<IAutoEditStrategy> ret = new ArrayList<IAutoEditStrategy>();
        	
        	IAutoEditStrategy ss[] = super.getAutoEditStrategies(sourceViewer, contentType);
        	
        	ret.add(new SVAutoIndentStrategy(fEditor, partitioning));
        	for (IAutoEditStrategy si : ss) {
        		ret.add(si);
        	}
        	
    		return ret.toArray(new IAutoEditStrategy[ret.size()]); 
        }
	}
	
	@Override
	public String[] getConfiguredContentTypes(ISourceViewer viewer) {
		return new String[] {
				IDocument.DEFAULT_CONTENT_TYPE,
				SVDocumentPartitions.SV_MULTILINE_COMMENT,
				SVDocumentPartitions.SV_SINGLELINE_COMMENT,
				SVDocumentPartitions.SV_STRING,
				SVDocumentPartitions.SV_KEYWORD
		};
	}
	
	/*
	@Override
	public ITextDoubleClickStrategy getDoubleClickStrategy(
			ISourceViewer sourceViewer, String contentType) {
		return new SVDoubleClickStrategy();
	}
	 */

	@Override
	public IPresentationReconciler getPresentationReconciler(
			ISourceViewer		viewer) {
		PresentationReconciler r = new SVPresentationReconciler();
		
		r.setDocumentPartitioning(
				getConfiguredDocumentPartitioning(viewer));
		
		DefaultDamagerRepairer dr;
		
		if (fEditor != null) {
			dr = new DefaultDamagerRepairer(fEditor.getCodeScanner());
		} else {
			dr = new DefaultDamagerRepairer(new SVCodeScanner());
		}
		
		r.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		r.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
		
		BufferedRuleBasedScanner scanner;
		
		scanner = new BufferedRuleBasedScanner(1); 
		scanner.setDefaultReturnToken(new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.MULTI_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.MULTI_LINE_COMMENT))));
		dr = new DefaultDamagerRepairer(scanner);
		r.setDamager(dr, SVDocumentPartitions.SV_MULTILINE_COMMENT);
		r.setRepairer(dr, SVDocumentPartitions.SV_MULTILINE_COMMENT);
		
		scanner = new BufferedRuleBasedScanner(1);
		scanner.setDefaultReturnToken(new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SINGLE_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.SINGLE_LINE_COMMENT))));
		dr = new DefaultDamagerRepairer(scanner);
		r.setDamager(dr, SVDocumentPartitions.SV_SINGLELINE_COMMENT);
		r.setRepairer(dr, SVDocumentPartitions.SV_SINGLELINE_COMMENT);
		
		/*
		scanner = new BufferedRuleBasedScanner(1);
		scanner.setDefaultReturnToken(new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.STRING),
				null, SVEditorColors.getStyle(SVEditorColors.STRING))));
		dr = new DefaultDamagerRepairer(scanner);
		r.setDamager(dr, SVDocumentPartitions.SV_STRING);
		r.setRepairer(dr, SVDocumentPartitions.SV_STRING);
		 */
		
		
		return r;
	}

	@Override
	public String getConfiguredDocumentPartitioning(ISourceViewer viewer) {
		return SVDocumentPartitions.SV_PARTITIONING;
	}

	@Override
	public IReconciler getReconciler(ISourceViewer viewer) {
		return new MonoReconciler(new SVReconcilingStrategy(fEditor), false);
	}
	
	@Override
	public IAnnotationHover getAnnotationHover(ISourceViewer viewer) {
		return new DefaultAnnotationHover();
	}

	@Override
	public String[] getDefaultPrefixes(ISourceViewer sourceViewer, String contentType) {
		return new String[] {"//", ""};
	}
	
	public ITextHover getTextHover(ISourceViewer viewer, String contentType) {
		if (!contentType.equals(SVDocumentPartitions.SV_STRING) &&
			!contentType.equals(SVDocumentPartitions.SV_MULTILINE_COMMENT) &&
			!contentType.equals(SVDocumentPartitions.SV_SINGLELINE_COMMENT)) {
//			return new SVEditorTextHover(fEditor, viewer) ;
//			SVDocHover hover = new SVDocHover() ;
			ISVEditorTextHover hover = new SVDocHover() ;
			hover.setEditor(fEditor) ;
			return hover ;
		}
		return null;
	}
	
	private IInformationControlCreator getObjectsPresenterControlCreator(ISourceViewer sourceViewer, final String commandId) {
		return new IInformationControlCreator() {
			public IInformationControl createInformationControl(Shell parent) {
				IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
				Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
				Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));	
				int shellStyle= SWT.RESIZE;
				int treeStyle= SWT.V_SCROLL | SWT.H_SCROLL;
				ObjectsInformationControl obj = new ObjectsInformationControl(parent, shellStyle, treeStyle, commandId);
				obj.setBackgroundColor(bg_color);
				obj.setForegroundColor(fg_color);
				return obj;
			}
		};
	}	
	
	private IInformationControlCreator getOutlinePresenterControlCreator(ISourceViewer sourceViewer, final String commandId) {
		return new IInformationControlCreator() {
			public IInformationControl createInformationControl(Shell parent) {
				IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
				Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
				Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));	
				int shellStyle= SWT.RESIZE;
				int treeStyle= SWT.V_SCROLL | SWT.H_SCROLL;
				OutlineInformationControl outline = new OutlineInformationControl(parent, shellStyle, treeStyle, commandId);
				outline.setBackgroundColor(bg_color);
				outline.setForegroundColor(fg_color);
				
				return outline;
			}
		};
	}	
	
	private IInformationControlCreator getHierarchyPresenterControlCreator(ISourceViewer sourceViewer, final String commandId) {
		return new IInformationControlCreator() {
			public IInformationControl createInformationControl(Shell parent) {
				IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
				Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
				Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
						prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));	
				int shellStyle= SWT.RESIZE;
				int treeStyle= SWT.V_SCROLL | SWT.H_SCROLL;
				HierarchyInformationControl h = new HierarchyInformationControl(parent, shellStyle, treeStyle, commandId) ;
				
				h.setBackgroundColor(bg_color);
				h.setForegroundColor(fg_color);
				
				return h;
			}
		};
	}	
	
	public IInformationPresenter getObjectsPresenter(ISourceViewer sourceViewer, boolean doCodeResolve) {
		InformationPresenter presenter;
		
		presenter = new InformationPresenter(
				getObjectsPresenterControlCreator(sourceViewer, 
						SVUiPlugin.PLUGIN_ID + ".editor.open.quick.objects")) ;
		presenter.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
		presenter.setAnchor(AbstractInformationControlManager.ANCHOR_GLOBAL);
		IInformationProvider provider = new SVEditorProvider(fEditor);
		for (String ct : getConfiguredContentTypes(sourceViewer)) {
			presenter.setInformationProvider(provider, ct);
		}
		presenter.setSizeConstraints(50, 20, true, false);

		return presenter;
	}	
	
	public IInformationPresenter getOutlinePresenter(ISourceViewer sourceViewer, boolean doCodeResolve) {
		InformationPresenter presenter;
		presenter= new InformationPresenter(
				getOutlinePresenterControlCreator(sourceViewer, 
						SVUiPlugin.PLUGIN_ID + ".editor.open.quick.outline")) ;
		presenter.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
		presenter.setAnchor(AbstractInformationControlManager.ANCHOR_GLOBAL);
		IInformationProvider provider = new SVEditorProvider(fEditor);
		for (String ct : getConfiguredContentTypes(sourceViewer)) {
			presenter.setInformationProvider(provider, ct);
		}
		presenter.setSizeConstraints(50, 20, true, false);
		return presenter;
	}	
	
	public IInformationPresenter getHierarchyPresenter(ISourceViewer sourceViewer, boolean doCodeResolve) {
		InformationPresenter presenter;
		presenter= new InformationPresenter(
				getHierarchyPresenterControlCreator(sourceViewer, 
						SVUiPlugin.PLUGIN_ID + ".editor.open.quick.hierarchy")) ;
		presenter.setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));
		presenter.setAnchor(AbstractInformationControlManager.ANCHOR_GLOBAL);
		IInformationProvider provider = new SVElementProvider(fEditor); 
		for (String ct : getConfiguredContentTypes(sourceViewer)) {
			presenter.setInformationProvider(provider, ct);
		}
		presenter.setSizeConstraints(50, 20, true, false);
		return presenter;
	}	
	
}
