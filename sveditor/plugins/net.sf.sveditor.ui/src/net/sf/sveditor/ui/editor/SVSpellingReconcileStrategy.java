package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.spelling.SpellingReconcileStrategy;
import org.eclipse.ui.texteditor.spelling.SpellingService;

public class SVSpellingReconcileStrategy extends SpellingReconcileStrategy {
	
	public SVSpellingReconcileStrategy(
			ISourceViewer 		viewer, 
			SpellingService 	spelling_service) {
		super(viewer, spelling_service);
	}

	@SuppressWarnings("unchecked")
	@Override
	public void reconcile(IRegion region) {
		List<Annotation> ann_list_total = new ArrayList<Annotation>();
		List<Position> 	 pos_list_total = new ArrayList<Position>();
		IAnnotationModel model = getAnnotationModel();
		
		ITypedRegion regions[] = null;
		
		try {
			regions = TextUtilities.computePartitioning(
					getDocument(), SVDocumentPartitions.SV_PARTITIONING,
					region.getOffset(), region.getLength(), false);
		} catch (BadLocationException e) {}
		
	
		for (ITypedRegion r : regions) {
			if (SVDocumentPartitions.SV_MULTILINE_COMMENT.equals(r.getType()) ||
					SVDocumentPartitions.SV_SINGLELINE_COMMENT.equals(r.getType())) {
				super.reconcile(r);
				Iterator<Annotation> it = model.getAnnotationIterator();
				while (it.hasNext()) {
					Annotation ann = (Annotation)it.next();
					ann_list_total.add(ann);
					pos_list_total.add(model.getPosition(ann));
				}
			}
		}
		
		Iterator<Annotation> it = model.getAnnotationIterator();
		while (it.hasNext()) {
			Annotation ann = (Annotation)it.next();
			int idx = ann_list_total.indexOf(ann);
			if (idx != -1) {
				ann_list_total.remove(idx);
				pos_list_total.remove(idx);
			}
		}

		for (int i=0; i<ann_list_total.size(); i++) {
			Annotation ann = ann_list_total.get(i);
			Position pos = pos_list_total.get(i);
			model.addAnnotation(ann, pos);
		}
	}

}
