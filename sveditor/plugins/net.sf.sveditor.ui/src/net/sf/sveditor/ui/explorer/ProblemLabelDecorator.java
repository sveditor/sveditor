/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;

public class ProblemLabelDecorator extends LabelProvider implements ILightweightLabelDecorator {

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
}
