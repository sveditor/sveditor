/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

public class SVTodoScanner implements IResourceChangeListener,
		IResourceDeltaVisitor {
	
	public SVTodoScanner() {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
	}
	
	public void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}

	
	public void resourceChanged(IResourceChangeEvent event) {
//		System.out.println("resourceChanged: " + event.getDelta());
		if (event.getDelta() != null) {
			try {
				event.getDelta().accept(this);
			} catch (CoreException e) { }
		}
	}

	
	public boolean visit(IResourceDelta delta) throws CoreException {
		if (delta.getResource() instanceof IFile) {
			IFile file = (IFile)delta.getResource();
			
			if (isSVFile(file)) {
				file.deleteMarkers(IMarker.TASK, true, IResource.DEPTH_ONE);
				
			}
		}
		return true;
	}
	
	private static final String suffixes[] = {
		".sv",
		".svh",
		".v",
		".vl",
		".vlog",
		".vh"
	};
	
	private boolean isSVFile(IFile f) {
		for (String s : suffixes) {
			if (f.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
	}
}
