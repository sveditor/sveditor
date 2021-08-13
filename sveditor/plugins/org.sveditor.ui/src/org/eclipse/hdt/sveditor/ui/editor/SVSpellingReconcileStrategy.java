/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModel;
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
		AnnotationModel model = (AnnotationModel)getAnnotationModel();
		
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
		List<Annotation> remove_ann = new ArrayList<Annotation>();
		Map<Annotation, Position> add_ann = new HashMap<Annotation, Position>();
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
					remove_ann.add(ann);
				}
			} else if (ann != null) {
				remove_ann.add(ann);
			}
		}
		
		// Now, place the new annotations
		for (SpellingProblem problem : fProblems) {
			Annotation ann = new SpellingAnnotation(problem);
			add_ann.put(ann, new Position(problem.getOffset(), problem.getLength()));
		}
		model.replaceAnnotations(
				remove_ann.toArray(new Annotation[remove_ann.size()]), 
				add_ann);
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
