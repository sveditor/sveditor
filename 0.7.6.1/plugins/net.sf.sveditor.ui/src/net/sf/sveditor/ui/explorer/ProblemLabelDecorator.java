package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;

public class ProblemLabelDecorator implements ILightweightLabelDecorator {


	public void decorate(Object element, IDecoration decoration) {
		if (!(element instanceof IResource)) {
			return;
		}
		IWorkbench workbench = PlatformUI.getWorkbench();
		if (workbench.isClosing()) {
			return;
		}

		IResource res = (IResource) element;

		try {
			if (res.findMaxProblemSeverity(IMarker.PROBLEM, true, IResource.DEPTH_INFINITE) >= IMarker.SEVERITY_ERROR) {
				ImageDescriptor image = SVUiPlugin.getImageDescriptor(
						"/icons/ovr16/error_co.gif");
				if (image != null) {
					decoration.addOverlay(image);
				}
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public void addListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub
		
	}

	public void dispose() {
		// TODO Auto-generated method stub
		
	}

	public boolean isLabelProperty(Object element, String property) {
		// TODO Auto-generated method stub
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub
		
	}
}
