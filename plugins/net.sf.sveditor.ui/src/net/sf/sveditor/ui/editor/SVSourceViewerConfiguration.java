package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistant;
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

public class SVSourceViewerConfiguration extends SourceViewerConfiguration {
	private SVEditor				fEditor;
	private ContentAssistant		fContentAssist;
	
	public SVSourceViewerConfiguration(SVEditor editor) {
		fEditor = editor;
	}
	
	
	
	
	@Override
	public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
		if (fContentAssist == null) {
			fContentAssist = new ContentAssistant();
			SVCompletionProcessor p = new SVCompletionProcessor();
			p.init(fEditor);

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
		
		
		// TODO Auto-generated method stub
		return super.getAutoEditStrategies(sourceViewer, contentType);
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
	
	@Override
	public IPresentationReconciler getPresentationReconciler(
			ISourceViewer		viewer) {
		PresentationReconciler r = new SVPresentationReconciler();
		
		r.setDocumentPartitioning(
				getConfiguredDocumentPartitioning(viewer));
		
		DefaultDamagerRepairer dr = 
			new DefaultDamagerRepairer(fEditor.getCodeScanner());
		
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
	public ITextHover getTextHover(ISourceViewer viewer, String contentType) {
		// TODO:
		return super.getTextHover(viewer, contentType);
		// return new SVTextHover(viewer);
	}
}
