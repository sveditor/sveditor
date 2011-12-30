package net.sf.sveditor.ui.compare;

import net.sf.sveditor.ui.editor.SVSourceViewerConfiguration;

import org.eclipse.compare.CompareConfiguration;
import org.eclipse.compare.contentmergeviewer.TextMergeViewer;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.swt.widgets.Composite;

public class SVCompareViewer extends TextMergeViewer {

	public SVCompareViewer(Composite parent, CompareConfiguration configuration) {
		super(parent, configuration);
		System.out.println("SVMergeViewer");
	}
	
	public SVCompareViewer(Composite parent, int arg1, CompareConfiguration configuration) {
		super(parent, arg1, configuration);
		System.out.println("SVMergeViewer");
	}

	@Override
	protected void configureTextViewer(TextViewer textViewer) {
		if(textViewer instanceof ISourceViewer){
			SVSourceViewerConfiguration configuration = new SVSourceViewerConfiguration(null);
			((ISourceViewer)textViewer).configure(configuration);
		}
	}
	
}
