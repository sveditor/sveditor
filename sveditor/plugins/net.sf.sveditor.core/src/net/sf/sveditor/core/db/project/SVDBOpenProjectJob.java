package net.sf.sveditor.core.db.project;

import net.sf.sveditor.core.SVCorePlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBOpenProjectJob extends Job {
	IProject			fProject;
	
	public SVDBOpenProjectJob(IProject p) {
		super("Opening Project " + p.getName());
		fProject = p;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		if (SVDBProjectManager.isSveProject(fProject)) {
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			monitor.beginTask("Opening SV Project " + fProject.getName(), 1000);
			SVDBProjectData pdata = pmgr.getProjectData(fProject);
			monitor.done();
		}

		return Status.OK_STATUS;
	}

}
