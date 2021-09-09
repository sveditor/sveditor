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
package org.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.sveditor.core.ISVProjectDelayedOp;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

public class SVProjectDelayedBuild extends Job implements ISVProjectDelayedOp {
	private SVDBProjectManager		fProjectMgr;
	private List<IProject>			fProjects;
	private LogHandle				fLog;
	
	public SVProjectDelayedBuild(
			SVDBProjectManager			pmgr,
			IProject 					p) {
		super("");
		fProjectMgr = pmgr;
		fProjects = new ArrayList<IProject>();
		fProjects.add(p);
		fLog = LogFactory.getLogHandle("SVProjectDelayedBuild");
	}
	
	public void projectBuildStarted(IProject p) {
		synchronized (fProjects) {
			fProjects.remove(p);
		}
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		fProjectMgr.startDelayedBuild(this);
		
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Build Projects", 10000*fProjects.size());
		
		for (IProject p : fProjects) {
			try {
				p.build(IncrementalProjectBuilder.FULL_BUILD, 
					subMonitor.newChild(10000));
			} catch (CoreException e) {
				fLog.error("Build of project " + p.getName() + " failed", e);
			}
		}
		
		subMonitor.done();
	
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
