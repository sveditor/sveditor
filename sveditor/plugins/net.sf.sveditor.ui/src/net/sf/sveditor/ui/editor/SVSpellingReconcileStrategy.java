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
import org.eclipse.ui.texteditor.spelling.ISpellingProblemCollector;
import org.eclipse.ui.texteditor.spelling.SpellingAnnotation;
import org.eclipse.ui.texteditor.spelling.SpellingProblem;
import org.eclipse.ui.texteditor.spelling.SpellingReconcileStrategy;
import org.eclipse.ui.texteditor.spelling.SpellingService;

public class SVSpellingReconcileStrategy extends SpellingReconcileStrategy {
	private List<SpellingProblem>			fProblems = new ArrayList<SpellingProblem>();
	
	public SVSpellingReconcileStrategy(
			ISourceViewer 		viewer, 
			SpellingService 	spelling_service) {
		super(viewer, spelling_service);
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public void reconcile(IRegion region) {
		IAnnotationModel model = getAnnotationModel();
		
		if (model == null) {
			return;
		}
		
		fProblems.clear();
		
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
			}
		}
	
		// Remove any annotations inside the regions
		Iterator<Annotation> it = model.getAnnotationIterator();
		while (it.hasNext()) {
			Annotation ann = (Annotation)it.next();
			
			if (ann == null || !ann.getType().equals(SpellingAnnotation.TYPE)) {
				continue;
			}
			
			Position pos = model.getPosition(ann);

			if (pos != null) {
				boolean in_region = false;
				for (ITypedRegion r : regions) {
					if (r == null) {
						continue;
					}
					if (pos.getOffset() >= r.getOffset() &&
							pos.getOffset() < r.getOffset()+r.getLength()) {
						in_region = true;
						break;
					}
				}

				if (in_region) {
					model.removeAnnotation(ann);
				}
			} else if (ann != null) {
				model.removeAnnotation(ann);
			}
		}
		
		// Now, place the new annotations
		for (SpellingProblem problem : fProblems) {
			Annotation ann = new SpellingAnnotation(problem);
			model.addAnnotation(ann, new Position(problem.getOffset(), problem.getLength()));
		}
	}
	
	@Override
	protected ISpellingProblemCollector createSpellingProblemCollector() {
		return fSpellingProblemCollector;
	}

	private ISpellingProblemCollector			fSpellingProblemCollector = new ISpellingProblemCollector() {
		
		public void endCollecting() { }
		
		public void beginCollecting() { }
		
		public void accept(SpellingProblem problem) {
			fProblems.add(problem);
		}
	};
}
