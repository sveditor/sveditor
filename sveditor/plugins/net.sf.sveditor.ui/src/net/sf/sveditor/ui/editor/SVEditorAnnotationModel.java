package net.sf.sveditor.ui.editor;

import org.eclipse.core.resources.IResource;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;

public class SVEditorAnnotationModel extends ResourceMarkerAnnotationModel {
	
	public SVEditorAnnotationModel(IResource resource) {
		super(resource);
		listenToMarkerChanges(false);
	}

}
