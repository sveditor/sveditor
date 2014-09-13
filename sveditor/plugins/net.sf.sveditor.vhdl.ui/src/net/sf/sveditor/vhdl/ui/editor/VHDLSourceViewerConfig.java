package net.sf.sveditor.vhdl.ui.editor;

import net.sf.sveditor.ui.editor.SVEditorColors;

import org.eclipse.jface.text.IDocument;
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
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

public class VHDLSourceViewerConfig extends SourceViewerConfiguration {
	public static final String			VHD_COMMENT = "__vhd_comment";
	public static final String			VHD_STRING  = "__vhd_string";
	public static final String			VHD_KEYWORD = "__vhd_keyword";
	
	private VHDLEditor						fEditor;
	private ContentAssistant				fContentAssist;
	
	public VHDLSourceViewerConfig(VHDLEditor editor) {
		fEditor = editor;
		
	}
	
	public String[] getConfiguredContentTypes(ISourceViewer viewer) {
		return new String[] {
				IDocument.DEFAULT_CONTENT_TYPE,
				VHD_COMMENT,
				VHD_STRING,
				VHD_KEYWORD
		};
	}
	
	
	
	@Override
	public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
		if (fContentAssist == null) {
			fContentAssist = new ContentAssistant();
			VHDLContentAssistProvider p = new VHDLContentAssistProvider();
			
			fContentAssist.setContentAssistProcessor(p,
					IDocument.DEFAULT_CONTENT_TYPE);
			fContentAssist.setInformationControlCreator(
					getInformationControlCreator(sourceViewer));
			fContentAssist.enableAutoActivation(true);
			fContentAssist.enableAutoInsert(true);
			fContentAssist.enablePrefixCompletion(true);
		}
		
		return fContentAssist;
	}

	@Override
	public IPresentationReconciler getPresentationReconciler(
			ISourceViewer sourceViewer) {
		PresentationReconciler r = new VHDLPresentationReconciler();
		
		r.setDocumentPartitioning(
				getConfiguredDocumentPartitioning(sourceViewer));
		
		DefaultDamagerRepairer dr = 
			new DefaultDamagerRepairer(fEditor.getCodeScanner());
		
		r.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		r.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
		
		BufferedRuleBasedScanner scanner;
		
		scanner = new BufferedRuleBasedScanner(1);
		scanner.setDefaultReturnToken(new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.SINGLE_LINE_COMMENT),
				null, SVEditorColors.getStyle(SVEditorColors.SINGLE_LINE_COMMENT))));
		dr = new DefaultDamagerRepairer(scanner);
		r.setDamager(dr, VHD_COMMENT);
		r.setRepairer(dr, VHD_COMMENT);

		scanner = new BufferedRuleBasedScanner(1);
		scanner.setDefaultReturnToken(new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.STRING),
				null, SVEditorColors.getStyle(SVEditorColors.STRING))));
		dr = new DefaultDamagerRepairer(scanner);
		r.setDamager(dr, VHD_STRING);
		r.setRepairer(dr, VHD_STRING);
		
		
		return r;
	}

	@Override
	public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer) {
		return VHDLDocumentPartitions.VHD_PARTITIONING;
	}

	@Override
	public IReconciler getReconciler(ISourceViewer sourceViewer) {
		return new MonoReconciler(new VHDLReconcilingStrategy(fEditor), false);
	}

}
