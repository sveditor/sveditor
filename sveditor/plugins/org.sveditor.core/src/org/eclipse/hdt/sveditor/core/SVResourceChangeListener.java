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
package org.eclipse.hdt.sveditor.core;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexResourceChangeEvent.Type;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;

public class SVResourceChangeListener implements IResourceChangeListener {
	private SVDBProjectManager				fProjectMgr;
	private boolean							fResourceListenerActive;
	// Project-import 
	private Set<IProject>					fPendingOpenProjects;
	
	
	public SVResourceChangeListener(SVDBProjectManager pmgr) {
		fProjectMgr = pmgr;
		fPendingOpenProjects = new HashSet<IProject>();
		init();
	}

	public synchronized void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
		fResourceListenerActive = false;
	}
	
	public synchronized void init() {
		if (!fResourceListenerActive) {
			ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
			fResourceListenerActive = true;
		}
	}

	public void resourceChanged(IResourceChangeEvent event) {
		final List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
	
		debug("--> resourceChanged");
		String type = "UNKNOWN";
		switch (event.getType()) {
			case IResourceChangeEvent.PRE_CLOSE: type = "PRE_CLOSE"; break;
			case IResourceChangeEvent.PRE_BUILD: type = "PRE_BUILD"; break;
			case IResourceChangeEvent.PRE_DELETE: type = "PRE_DELETE"; break;
			case IResourceChangeEvent.PRE_REFRESH: type = "PRE_REFRESH"; break;
			case IResourceChangeEvent.POST_BUILD: type = "POST_BUILD"; break;
			case IResourceChangeEvent.POST_CHANGE: type = "POST_CHANGE"; break;
		}
		debug("resourceChanged: " + type + " " + event.getResource());
		
		if (event.getDelta() == null) {

			debug("Null delta: " + type + " " + event.getResource());
		} else if (event.getResource() instanceof IProject) {
			debug("Change to project");
		} else {

			SVResourceVisitor visitor = new SVResourceVisitor();

			visitor.begin();
			try {
				event.getDelta().accept(visitor);
			} catch (CoreException e) {}
			visitor.end();
		}
		
		if (changes.size() > 0) {
			// 
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			rgy.notifyChanges(changes);
		}
		debug("<-- resourceChanged");
	}
	
	private class SVResourceVisitor implements IResourceDeltaVisitor {
		private List<IProject> 		fAffectedProjects;
		private List<IProject>		fOpenedProjects;
		private List<IProject>		fClosedProject;
		private boolean				fNonProjectDeltasSeen;
		
		public SVResourceVisitor() {
			fAffectedProjects = new ArrayList<IProject>();
			fOpenedProjects = new ArrayList<IProject>();
			fClosedProject = new ArrayList<IProject>();
		}
		
		public void begin() {
		}
		
		public void end() {
			debug("SVResourceChange end() fOpenedProjects.size=" + fOpenedProjects.size() +
					" fAffectedProjects.size=" + fAffectedProjects.size());
			
//			if (fOpenedProjects.size() > 0) {

				// Eclipse appears to import a project in two steps. The first
				// step is to just import the project and .project file. The
				// second step populates the project with files
				if (!fNonProjectDeltasSeen) {
					debug("No no-project deltas seen");
					for (IProject p : fOpenedProjects) {
						synchronized (fPendingOpenProjects) {
							if (!fPendingOpenProjects.contains(p)) {
								fPendingOpenProjects.add(p);
							}
						}
					}
				} else {
					debug("Non-project deltas seen");
					for (IProject p : fAffectedProjects) {
						debug("  Affected project: " + p.getName());
						if (fPendingOpenProjects.contains(p)) {
							debug("  Project opened: " + p.getName());
							fProjectMgr.projectOpened(p);
							fPendingOpenProjects.remove(p);
						}
					}
				}
//			}
			
			for (IProject p : fClosedProject) {
				fProjectMgr.projectClosed(p);
			}

			/*
			for (IProject p : fAffectedProjects) {
				debug("AffectedProject: " + p.getName());
				
				synchronized (fPendingOpenProjects) {
					if (fPendingOpenProjects.contains(p)) {
						fPendingOpenProjects.remove(p);
						debug("  Project opened: " + p.getName());
						fProjectMgr.projectOpened(p);
					}
				}
			}
			 */
		}

		public boolean visit(IResourceDelta delta) throws CoreException {
			
			String kind = "UNKNOWN";
			SVDBIndexResourceChangeEvent.Type type = null;
			switch (delta.getKind()) {
				case IResourceDelta.ADDED: 
					type = Type.ADD;
					kind = "ADDED"; 
					break;
				case IResourceDelta.CHANGED: 
					// We don't care about changes like markers
					if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
						type = Type.CHANGE;
					}
					kind = "CHANGED"; 
					break;
				case IResourceDelta.OPEN: kind = "OPEN"; break;
				case IResourceDelta.SYNC: kind = "SYNC"; break;
				case IResourceDelta.REMOVED: 
					type = Type.REMOVE;
					kind = "REMOVED"; 
					break;
			}
			
			if (delta.getResource() instanceof IProject) {
				IProject p = (IProject)delta.getResource();
				if ((delta.getFlags() & IResourceDelta.OPEN) != 0) {
					debug("delta: Project open/close -- " + delta.getFlags());
					if (p.isOpen()) {
						// Project opening or added
						if (!fOpenedProjects.contains(p)) {
							fOpenedProjects.add(p);
						}
					} else {
						// Project closing
						if (!fClosedProject.contains(p)) {
							fClosedProject.add(p);
						}
					}
				} else if (delta.getKind() == IResourceDelta.REMOVED) {
					fProjectMgr.projectRemoved(p);
				}
			} else {
				String name = delta.getResource().getName();
				IProject p = delta.getResource().getProject();
				if (p != null && !fAffectedProjects.contains(p)) {
					fAffectedProjects.add(p);
				}
				if (!name.trim().equals("") && !name.equals(".project")) {
					fNonProjectDeltasSeen = true;
				}
				if (delta.getResource() instanceof IFile) {
					if (type != null) {
						debug("Delta " + kind + " " + 
								Integer.toHexString(delta.getFlags()) + " " +
								delta.getResource().getFullPath());
					}
				} else {
					debug("delta: " + kind + " " + delta.getResource() + " " + 
							Integer.toHexString(delta.getFlags()));
				}
			}
			
			return true;
		}
	}

	private void debug(String msg) {
//		System.out.println(msg);
	}
}
