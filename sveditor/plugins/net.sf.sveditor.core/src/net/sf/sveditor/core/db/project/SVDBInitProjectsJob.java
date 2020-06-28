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
package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.builder.SVBuilderProcess;

public class SVDBInitProjectsJob extends Job implements ISVProjectDelayedOp {
	private List<IProject>				fProjects;
	private SVDBProjectManager			fProjectMgr;
	
	public SVDBInitProjectsJob(SVDBProjectManager pmgr) {
		super("Init SV Projects");
		
		fProjectMgr = pmgr;
		
		fProjects = new ArrayList<IProject>();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IProject projects[] = root.getProjects();
		
		for (IProject p : projects) {
			fProjects.add(p);
		}
	}
	
	public void projectBuildStarted(IProject p) {
		synchronized (fProjects) {
			fProjects.remove(p);
		}
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		List<IProject> sv_projects = new ArrayList<IProject>();
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		
		fProjectMgr.startDelayedBuild(this);

		synchronized (fProjects) {
			for (IProject p : fProjects) {
				if (p.isOpen()) {
					if (SVDBProjectManager.isSveProject(p)) {
						sv_projects.add(p);
					}
				}
			}
		}
		
		try {
			subMonitor.beginTask("Initializing SV Projects", 1000*sv_projects.size());
			for (IProject p : sv_projects) {
				// Ensure that this project has the SV nature
				SVProjectNature.ensureHasSvProjectNature(p);
				
				SubMonitor proj_loopMonitor = subMonitor.newChild(1000);
				SVBuilderProcess process = new SVBuilderProcess(proj_loopMonitor, p);
				
				SVCorePlugin.getDefault().getBuildProcessListener().buildProcess(process);
			
				process.init_project();
			}
		} finally {
			subMonitor.done();
		}

		return Status.OK_STATUS;
	}

	@Override
	public boolean containsProject(IProject p) {
		for (IProject pt : fProjects) {
			if (pt.equals(p)) {
				return true;
			}
		}
		return false;
	}
}
