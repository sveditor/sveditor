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

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBOpenProjectJob extends Job implements ISVProjectDelayedOp, ILogLevel {
	private SVDBProjectManager		fProjectMgr;
	private IProject				fProject;
	private IProject				fProjectSav;
	private LogHandle				fLog;
	
	public SVDBOpenProjectJob(SVDBProjectManager pmgr, IProject p) {
		super("Opening Project " + p.getName());
		fProjectMgr = pmgr;
		fProjectSav = fProject = p;
		
		fLog = LogFactory.getLogHandle("SVDBOpenProjectJob");
	}
	
	public void projectBuildStarted(IProject p) {
		if (fProject != null && p.equals(fProject)) {
			Exception e = null;
			
			try {
				throw new Exception();
			} catch (Exception ex) {
				e = ex;
			}
			fLog.debug(LEVEL_MIN, "-- projectBuildStarted(" + p.getName() + ") canceled", e);
			fProject = null;
		}
	}
	
	
	@Override
	public IStatus run(IProgressMonitor monitor) {
		SVDBProjectData pdata = null;
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		if (SVDBProjectManager.isSveProject(fProjectSav)) {
			// Ensure the project nature is associated
			SVProjectNature.ensureHasSvProjectNature(fProjectSav);
			
			pdata = pmgr.getProjectData(fProjectSav);
			pdata.init();
		}
		
		if (fProject == null) {
			fLog.debug(LEVEL_MIN, "-- OpenProjectJob canceled");
			return Status.OK_STATUS;
		}
		
		fLog.debug(LEVEL_MIN, "--> OpenProjectJob " + fProject.getName());
		
		fProjectMgr.startDelayedBuild(this);

		IWorkspaceDescription desc = ResourcesPlugin.getWorkspace().getDescription();
		
		if (!desc.isAutoBuilding() || SVCorePlugin.isTestModeBuilderDisabled()) {
			fLog.debug(LEVEL_MIN, "-- OpenProjectJob canceled -- AutoBuild disabled");
			return Status.OK_STATUS;
		}
		
		if (SVDBProjectManager.isSveProject(fProject)) {
			
			subMonitor.beginTask("Opening SV Project " + fProject.getName(), 1000);
			
			if (!pdata.haveDotSvProject()) {
				pdata.init();
			}
			
			// TODO: need to fire 'ProjectOpened' event
			
			try {
				fProject.build(IncrementalProjectBuilder.FULL_BUILD, 
					subMonitor.newChild(1000));
			} catch (CoreException e) {
				fLog.error("Project build failed", e);
			}
			subMonitor.done();
		} else {
			fLog.debug(LEVEL_MIN, "  Project " + fProject.getName() + " not an SVE project");
		}
		
		fLog.debug(LEVEL_MIN, "<-- OpenProjectJob " + fProject.getName());

		return Status.OK_STATUS;
	}

	@Override
	public boolean containsProject(IProject p) {
		return (fProject != null && fProject.equals(p));
	}
}
