package net.sf.sveditor.ui.argfile.editor;

import net.sf.sveditor.ui.editor.SVCodeScanner;
import net.sf.sveditor.ui.editor.SVEditorColors;
import net.sf.sveditor.ui.editor.SVPresentationReconciler;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
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

public class SVArgFileSourceViewerConfiguration extends
		SourceViewerConfiguration {
	private SVArgFileEditor				fEditor;
	private ContentAssistant			fContentAssist;
	
	public SVArgFileSourceViewerConfiguration(SVArgFileEditor editor) {
		 fEditor = editor;
	}
	
	@Override
	public IReconciler getReconciler(ISourceViewer sourceViewer) {
		return new MonoReconciler(new SVArgFileReconcilingStrategy(fEditor), false);
	}
	
	@Override
	public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer) {
		return new DefaultAnnotationHover();
	}

	@Override
	public IPresentationReconciler getPresentationReconciler(ISourceViewer viewer) {
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
		r.setDamager(dr, SVArgFileDocumentPartitions.SV_ARGFILE_MULTILINE_COMMENT);
		r.setRepairer(dr, SVArgFileDocumentPartitions.SV_ARGFILE_MULTILINE_COMMENT);
		
		scanner = new BufferedRuleBasedScanner(1);
		scanner.setDefaultReturnToken(new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SINGLE_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.SINGLE_LINE_COMMENT))));
		dr = new DefaultDamagerRepairer(scanner);
		r.setDamager(dr, SVArgFileDocumentPartitions.SV_ARGFILE_SINGLELINE_COMMENT);
		r.setRepairer(dr, SVArgFileDocumentPartitions.SV_ARGFILE_SINGLELINE_COMMENT);
		
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
	public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
		return new String[] {
				IDocument.DEFAULT_CONTENT_TYPE,
				SVArgFileDocumentPartitions.SV_ARGFILE_MULTILINE_COMMENT,
				SVArgFileDocumentPartitions.SV_ARGFILE_SINGLELINE_COMMENT,
				SVArgFileDocumentPartitions.SV_ARGFILE_KEYWORD
		};
	}

	@Override
	public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer) {
		return SVArgFileDocumentPartitions.SV_ARGFILE_PARTITIONING;
	}

	@Override
	public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
		if (fContentAssist == null) {
			fContentAssist = new ContentAssistant();
			IContentAssistProcessor p = new SVArgFileCompletionProcessor(fEditor);

			fContentAssist.setContentAssistProcessor(p,
					IDocument.DEFAULT_CONTENT_TYPE);
			/*
			 */
			fContentAssist.setInformationControlCreator(
					getInformationControlCreator(sourceViewer));
			fContentAssist.enableAutoActivation(true);
			fContentAssist.enableAutoInsert(true);
			fContentAssist.enablePrefixCompletion(true);
		}
		
		return fContentAssist;		
	}

	
}
