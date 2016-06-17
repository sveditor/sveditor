package net.sf.sveditor.ui.views;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
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

import net.sf.sveditor.core.preproc.IPreProcListener;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.preproc.PreProcEvent;
import net.sf.sveditor.core.preproc.PreProcEvent.Type;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;


public class MacroExpansionView extends ViewPart {
	private ProjectionViewer						fProjectionViewer;
	private Document								fDocument;
	private Map<ProjectionAnnotation, Position>		fAnnotations;

	public MacroExpansionView() {
		fAnnotations = new HashMap<ProjectionAnnotation, Position>();
	}

	@Override
	public void createPartControl(Composite parent) {
		Composite c = new Composite(parent, SWT.None);
		c.setLayout(new GridLayout());
		
		CompositeRuler r = new CompositeRuler();
		OverviewRuler or = null; // new OverviewRuler(annotationAccess, width, sharedColors);
		fProjectionViewer = new ProjectionViewer(
				c, r, or, true, SWT.V_SCROLL+SWT.H_SCROLL);
		
		fProjectionViewer.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		IAnnotationAccess ann_access = new DefaultMarkerAnnotationAccess();
		ProjectionSupport ps = new ProjectionSupport(fProjectionViewer, ann_access, 
				EditorsPlugin.getDefault().getSharedTextColors());
				
		StringBuilder sb = new StringBuilder();
		
		for (int i=1; i<=20; i++) {
			sb.append("Line " + i + "\n");
		}
		fDocument = new Document("");
	
		fProjectionViewer.setDocument(
				fDocument, new ProjectionAnnotationModel());
		
		ps.install();
		
		// enableProjection must occur after setDocument, otherwise
		// certain things don't get hooked up correctly...
		fProjectionViewer.doOperation(ProjectionViewer.TOGGLE);
//		pv.enableProjection();
		
//		ProjectionAnnotation ann = new ProjectionAnnotation(true);
//		
//		Map<ProjectionAnnotation, Position> newAnn = new HashMap<ProjectionAnnotation, Position>();
//		newAnn.put(ann, new Position(10, 20));
//		
//		ProjectionAnnyotationModel pm = pv.getProjectionAnnotationModel();
//		
//		System.out.println("pm=" + pm);
//		if (pm != null) {
//		pm.modifyAnnotations(new Annotation[0], 
//				newAnn, new Annotation[0]);
//		}
	}

	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}
	
	public void setContext(SVEditor editor) {
		ITextSelection sel = editor.getTextSel();
		ISVStringPreProcessor pp = editor.createPreProcessor(-1);
		
		if (pp instanceof IPreProcMacroProvider) {
			IPreProcMacroProvider mp = (IPreProcMacroProvider)pp;
			
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
				
				SVPreProcessor.ReadMacroRef(sb, s, mp);
				
				final Stack<PreProcEvent> ev_stack = new Stack<PreProcEvent>();
				Set<ProjectionAnnotation> existing = 
						new HashSet<ProjectionAnnotation>(fAnnotations.keySet());
				fAnnotations.clear();

//				ProjectionAnnotation ann = new ProjectionAnnotation(true);
				ProjectionAnnotationModel pm = fProjectionViewer.getProjectionAnnotationModel();
				
				SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
				dp.addPreProcListener(new IPreProcListener() {
					
					@Override
					public void preproc_event(PreProcEvent event) {
						System.out.println("preproc_event: " + event.type + " " + event.text + " " + event.pos);
						if (event.type == Type.BeginExpand) {
							ev_stack.push(event);
						} else if (event.type == Type.EndExpand) {
							PreProcEvent begin_e = ev_stack.pop();
							ProjectionAnnotation ann = new ProjectionAnnotation(true);
							ann.getText();
							ann.setText(begin_e.text);
					
							System.out.println("Range: " + begin_e.pos + ".." + event.pos);
							fAnnotations.put(ann, new Position(
									begin_e.pos, event.pos-begin_e.pos));
						}
					}
				});
			
				System.out.println("Expand:\n" + sb.toString());
				String result = dp.expandMacro(sb.toString(), "FOO", 0);
				System.out.println("Result: " + result.length() + "\n" + result);
				
				fDocument.set(result);
		
				Annotation deletions[] = existing.toArray(
						new Annotation[existing.size()]);
				pm.modifyAnnotations(deletions, fAnnotations, new Annotation[0]);
			}
		} else {
			System.out.println("Error: not instanceof IPreProcMacroProvider");
		}
	}

}
