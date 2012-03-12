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


package net.sf.sveditor.core;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.actions.WorkspaceModifyOperation;

/**
 * The marker propagation job is a singleton that queues up and
 * propagates markers. Markers are often created during event-propagation,
 * when they cannot be immediately applied to the workspace. 
 * 
 * @author ballance
 *
 */
public class SVMarkerPropagationJob extends Job {
	private class MarkerInfo {
		IFile				fFile;
		int					fSeverity;
		int					fLineno;
		String				fMsg;
	}
	
	private List<MarkerInfo>		fMarkerList;
	
	public SVMarkerPropagationJob() {
		super("SVEditor Marker Propagation");
		fMarkerList = new ArrayList<SVMarkerPropagationJob.MarkerInfo>();
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		final List<MarkerInfo> markers = new ArrayList<SVMarkerPropagationJob.MarkerInfo>(); 
		synchronized (fMarkerList) {
			markers.addAll(fMarkerList);
			fMarkerList.clear();
		}
		
		WorkspaceModifyOperation op = new WorkspaceModifyOperation() {

			@Override
			protected void execute(IProgressMonitor monitor) throws CoreException,
				InvocationTargetException, InterruptedException {
				IMarker marker = null;
				for (MarkerInfo info : markers) {
					try {
						marker = info.fFile.createMarker(IMarker.PROBLEM);
						marker.setAttribute(IMarker.SEVERITY, info.fSeverity);
						marker.setAttribute(IMarker.LINE_NUMBER, info.fLineno);
						marker.setAttribute(IMarker.MESSAGE, info.fMsg);
					} catch (CoreException e) {
						if (marker != null) {
							marker.delete();
						}
					}
				}
			}
		};

		try {
			op.run(monitor);
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return Status.OK_STATUS;
	}
	
	
	public void addMarker(IFile file, int severity, int lineno, String msg) {
		MarkerInfo info = new MarkerInfo();
		info.fFile = file;
		info.fSeverity = severity;
		info.fLineno = lineno;
		info.fMsg = msg;
		
		synchronized (fMarkerList) {
			fMarkerList.add(info);
		}

		synchronized (this) {
			if (getState() == Job.NONE) {
				schedule(1);
			}
		}
	}

}
