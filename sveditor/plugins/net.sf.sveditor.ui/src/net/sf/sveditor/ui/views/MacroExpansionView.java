package net.sf.sveditor.ui.views;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
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


public class MacroExpansionView extends ViewPart {

	public MacroExpansionView() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public void createPartControl(Composite parent) {
		Composite c = new Composite(parent, SWT.None);
		c.setLayout(new GridLayout());
		
//		TextViewer tv = new TextViewer(c, SWT.READ_ONLY);
//		VerticalRuler r = new VerticalRuler(12);
		CompositeRuler r = new CompositeRuler();
//		VerticalRuler r = new VerticalRuler(5);
		OverviewRuler or = null; // new OverviewRuler(annotationAccess, width, sharedColors);
		ProjectionViewer pv = new ProjectionViewer(c, r, or, true, 
				SWT.V_SCROLL+SWT.H_SCROLL) {

//					@Override
//					protected IAnnotationModel createVisualAnnotationModel(IAnnotationModel annotationModel) {
//						// TODO Auto-generated method stub
//						IAnnotationModel ret = super.createVisualAnnotationModel(annotationModel);
//						System.out.println("createVisualAnnotationModel: " + ret + " " + 
//								(ret instanceof IAnnotationModelExtension));
//						
//						System.out.println("    " + 
//								((IAnnotationModelExtension)ret).getAnnotationModel(ProjectionSupport.PROJECTION));
//						
//						
//						return ret;
//					}
			
		};
		
		pv.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		IAnnotationAccess ann_access = new DefaultMarkerAnnotationAccess();
		ProjectionSupport ps = new ProjectionSupport(pv, ann_access, 
				EditorsPlugin.getDefault().getSharedTextColors());
				
		StringBuilder sb = new StringBuilder();
		
		for (int i=1; i<=20; i++) {
			sb.append("Line " + i + "\n");
		}
		IDocument doc = new Document(sb.toString());
	
		pv.setDocument(doc, new ProjectionAnnotationModel());
		
		ps.install();
		
		// enableProjection must occur after setDocument, otherwise
		// certain things don't get hooked up correctly...
		pv.doOperation(ProjectionViewer.TOGGLE);
//		pv.enableProjection();
		
		ProjectionAnnotation ann = new ProjectionAnnotation(true);
		
		Map<ProjectionAnnotation, Position> newAnn = new HashMap<ProjectionAnnotation, Position>();
		newAnn.put(ann, new Position(10, 20));
		
		ProjectionAnnotationModel pm = pv.getProjectionAnnotationModel();
		
		System.out.println("pm=" + pm);
		if (pm != null) {
		pm.modifyAnnotations(new Annotation[0], 
				newAnn, new Annotation[0]);
		}
	}

	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}

}
