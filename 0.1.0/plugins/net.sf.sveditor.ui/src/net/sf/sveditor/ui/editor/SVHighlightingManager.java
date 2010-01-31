package net.sf.sveditor.ui.editor;

import java.util.EnumMap;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.source.SourceViewer;

public class SVHighlightingManager {
	
	private static EnumMap<SVEditorColors, TextAttribute>		fHighlightAttr;
	private SVHightingPresenter			fPresenter;
	private SVPresentationReconciler	fReconciler;
	
	static {
		if (fHighlightAttr == null) {
			EnumMap<SVEditorColors, TextAttribute> tmp = 
				new EnumMap<SVEditorColors, TextAttribute>(SVEditorColors.class);
			
			for (SVEditorColors c : new SVEditorColors[] {
					SVEditorColors.KEYWORD, SVEditorColors.STRING}) {
				tmp.put(c, new TextAttribute(SVEditorColors.getColor(c), 
						null, SVEditorColors.getStyle(c)));
			}
			fHighlightAttr = tmp;
		}
	}

	public void install(
			SourceViewer 				viewer, 
			SVPresentationReconciler 	rec, 
			SVEditor 		editor) {
		fPresenter = new SVHightingPresenter();
		/*
		fPresenter.install(viewer, rec);
		fReconciler = new SVPresentationReconciler();
		fReconciler.install(this, fPresenter, editor);
		 */
	}
	
	public TextAttribute getHighlight(SVEditorColors key) {
		System.out.println("getHighlight: " + key);
		return fHighlightAttr.get(key);
	}
}
