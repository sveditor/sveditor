package net.sf.sveditor.ui.argfile.editor;

import org.eclipse.core.resources.IResource;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;

public class SVArgFileAnnotationModel extends ResourceMarkerAnnotationModel {
	
	public SVArgFileAnnotationModel(IResource resource) {
		super(resource);
		
		listenToMarkerChanges(false);
	}

}
