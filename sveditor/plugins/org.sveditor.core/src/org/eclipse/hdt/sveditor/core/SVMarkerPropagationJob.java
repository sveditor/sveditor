/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

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
		IResource			fFile;
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
	
		/**
		WorkspaceModifyOperation op = new WorkspaceModifyOperation() {

			@Override
			protected void execute(IProgressMonitor monitor) throws CoreException,
				InvocationTargetException, InterruptedException {
		 */
			try {
				IMarker marker = null;
				for (MarkerInfo info : markers) {
					try {
						marker = info.fFile.createMarker(SVMarkers.TYPE_PROBLEM);
						marker.setAttribute(IMarker.SEVERITY, info.fSeverity);
						marker.setAttribute(IMarker.LINE_NUMBER, info.fLineno);
						marker.setAttribute(IMarker.MESSAGE, info.fMsg);
					} catch (CoreException e) {
						if (marker != null) {
							marker.delete();
						}
					}
				}
			} catch (CoreException e) {
				e.printStackTrace();
			}
		/*
			}
		};

		try {
			op.run(monitor);
		} catch (Exception e) {
			e.printStackTrace();
		}
		 */
		
		return Status.OK_STATUS;
	}
	
	
	public void addMarker(IResource file, int severity, int lineno, String msg) {
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
