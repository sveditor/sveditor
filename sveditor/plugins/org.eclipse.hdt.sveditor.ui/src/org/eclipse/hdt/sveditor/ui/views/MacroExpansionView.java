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
package org.eclipse.hdt.sveditor.ui.views;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.preproc.ISVStringPreProcessor;
import org.eclipse.hdt.sveditor.core.preproc.PreProcEvent;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcModelFactory;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcModelNode;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcessor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.CompositeRuler;
import org.eclipse.jface.text.source.IAnnotationAccess;
import org.eclipse.jface.text.source.OverviewRuler;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.internal.editors.text.EditorsPlugin;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.DefaultMarkerAnnotationAccess;

import org.eclipse.hdt.sveditor.ui.editor.SVDocumentPartitions;
import org.eclipse.hdt.sveditor.ui.editor.SVDocumentSetupParticipant;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.scanutils.SVDocumentTextScanner;


public class MacroExpansionView extends ViewPart {
	private ProjectionViewer						fProjectionViewer;
	private Document								fDocument;
	private Map<ProjectionAnnotation, Position>		fAnnotations;
	private MacroExpansionSourceViewerConfiguration	fSourceViewConfig;

	public MacroExpansionView() {
		fAnnotations = new HashMap<ProjectionAnnotation, Position>();
	}

	@Override
	public void createPartControl(Composite parent) {
		Composite c = new Composite(parent, SWT.None);
		c.setLayout(new GridLayout());
		
		CompositeRuler r = new CompositeRuler();
		OverviewRuler or = null; // new OverviewRuler(annotationAccess, width, sharedColors);
		fSourceViewConfig = new MacroExpansionSourceViewerConfiguration();
		fProjectionViewer = new ProjectionViewer(
				c, r, or, true, SWT.V_SCROLL+SWT.H_SCROLL);
		
		fProjectionViewer.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		IAnnotationAccess ann_access = new DefaultMarkerAnnotationAccess();
		ProjectionSupport ps = new ProjectionSupport(fProjectionViewer, ann_access, 
				EditorsPlugin.getDefault().getSharedTextColors());
		fProjectionViewer.getTextWidget().setFont(
				JFaceResources.getFont(JFaceResources.TEXT_FONT));

		StringBuilder sb = new StringBuilder();
		
		for (int i=1; i<=20; i++) {
			sb.append("Line " + i + "\n");
		}
		fDocument = new Document("");
		IDocumentPartitioner p = SVDocumentSetupParticipant.createPartitioner();
		fDocument.setDocumentPartitioner(SVDocumentPartitions.SV_PARTITIONING, p);
		p.connect(fDocument);
	
		fProjectionViewer.setDocument(
				fDocument, new ProjectionAnnotationModel());
	
		fProjectionViewer.configure(fSourceViewConfig);
		
		ps.install();
		
		// enableProjection must occur after setDocument, otherwise
		// certain things don't get hooked up correctly...
		fProjectionViewer.doOperation(ProjectionViewer.TOGGLE);
	}

	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}
	
	public void setContext(SVEditor editor) {
		ITextSelection sel = editor.getTextSel();
		ISVStringPreProcessor pp = editor.createPreProcessor(-1);
		
		fSourceViewConfig.setContentType(editor.getContentType());
		
		if (pp instanceof SVPreProcessor) {
//			IPreProcMacroProvider mp = (IPreProcMacroProvider)pp;
			SVPreProcessor preproc = (SVPreProcessor)pp;
			
			IDocument doc = editor.getDocument();
			int offset = -1, start = sel.getOffset();
			
			// Find the start of the macro
			try {
				// Scan backwards to find the tick
				if (doc.getChar(start) == '`') {
					offset = start;
				} else {
					while (start > 0) {
						if (doc.getChar(start) == '`' || 
								Character.isWhitespace(doc.getChar(start))) {
							break;
						}
						start--;
					}
					
					if (start > 0 && Character.isWhitespace(doc.getChar(start))) {
						// skip whitespace
						while (start > 0 && Character.isWhitespace(doc.getChar(start))) {
							start--;
						}
					}
					
					if (start >= 0 && doc.getChar(start) == '`') {
						offset = start;
					}
				}
			} catch (BadLocationException e) {
				e.printStackTrace();
			}

			if (offset != -1) {
				SVDocumentTextScanner s = new SVDocumentTextScanner(doc, offset);
				StringBuilder sb = new StringBuilder();
				
				SVPreProcessor.ReadMacroRef(sb, s, preproc.getMacroProvider());
				
				final Stack<PreProcEvent> ev_stack = new Stack<PreProcEvent>();
				Set<ProjectionAnnotation> existing = 
						new HashSet<ProjectionAnnotation>(fAnnotations.keySet());
				fAnnotations.clear();

//				ProjectionAnnotation ann = new ProjectionAnnotation(true);
		
				SVPreProcModelFactory factory = new SVPreProcModelFactory(pp);
				
				Tuple<SVPreProcModelNode, String> result = factory.build(sb.toString());
				
				StringBuilder content = new StringBuilder(result.second());
				
				if (result != null && result.first() != null) {
//					dump(result.second(), result.first());
					update_model(0, result.first(), content);
					fDocument.set(content.toString());

					ProjectionAnnotationModel pm = fProjectionViewer.getProjectionAnnotationModel();
					
					build_annotations(result.first(), fAnnotations);
					
					Annotation deletions[] = existing.toArray(
							new Annotation[existing.size()]);
					pm.modifyAnnotations(deletions, fAnnotations, new Annotation[0]);
				} else {
					fDocument.set("Macro appears to be undefined");
				}
			}
		} else {
			System.out.println("Error: not instanceof IPreProcMacroProvider: " +
					((pp == null)?"null":pp.getClass()));
//			fDocument.set("Internal Error: Failed to get a "
		}
	}

	// Take the preprocessed content:
	// - insert the unexpanded macro calls
	// - update the region start/end points
	private int update_model(int add, SVPreProcModelNode node, StringBuilder content) {
		node.setStart(node.getStart()+add);
		
		content.insert(node.getStart(), node.getText());
		
		add += node.getText().length();
		
		for (SVPreProcModelNode n : node.getChildren()) {
			add = update_model(add, n, content);
		}
		
		node.setEnd(node.getEnd()+add);
		
		// Ensure the End point is on a newline
		while (node.getEnd() < content.length()) {
			if (content.charAt(node.getEnd()) == '\n') {
				if (node.getEnd()+1 < content.length()) {
					node.setEnd(node.getEnd()+1);
				}
				break;
			} else {
				node.setEnd(node.getEnd()+1);
			}
		}
		
		return add;
	}
	
	private void dump(String doc, SVPreProcModelNode node) {
		System.out.println("--> dump " + node.getStart() + ".." + node.getEnd());
		System.out.println(doc.substring(node.getStart(), node.getEnd()));
		
		for (SVPreProcModelNode n : node.getChildren()) {
			dump(doc, n);
		}
		
		System.out.println("<-- dump " + node.getStart() + ".." + node.getEnd());
	}
	
	private void build_annotations(SVPreProcModelNode node, Map<ProjectionAnnotation, Position> annotations) {
		ProjectionAnnotation ann;
		ann = new ProjectionAnnotation(true);
		
		annotations.put(ann,  new Position(node.getStart(), 
				node.getEnd()-node.getStart()));
		
		for (SVPreProcModelNode n : node.getChildren()) {
			build_annotations(n, annotations);
		}
	}

}
