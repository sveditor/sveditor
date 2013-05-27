package net.sf.sveditor.core.db.project;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBOpenProjectJob extends Job {
	IProject			fProject;
	LogHandle			fLog;
	
	public SVDBOpenProjectJob(IProject p) {
		super("Opening Project " + p.getName());
		fProject = p;
		
		fLog = LogFactory.getLogHandle("SVDBOpenProjectJob");
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		if (SVDBProjectManager.isSveProject(fProject)) {
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			monitor.beginTask("Opening SV Project " + fProject.getName(), 1000);
			SVDBProjectData pdata = pmgr.getProjectData(fProject);
			try {
				fProject.build(IncrementalProjectBuilder.FULL_BUILD, 
					new SubProgressMonitor(monitor, 900));
			} catch (CoreException e) {
				fLog.error("Project build failed", e);
			}
			monitor.done();
		}

		return Status.OK_STATUS;
	}

}
