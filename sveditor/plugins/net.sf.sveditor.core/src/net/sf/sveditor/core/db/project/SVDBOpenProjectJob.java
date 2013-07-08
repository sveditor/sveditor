package net.sf.sveditor.core.db.project;

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectNature;
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

public class SVDBOpenProjectJob extends Job implements ISVProjectDelayedOp {
	private SVDBProjectManager		fProjectMgr;
	private IProject				fProject;
	private LogHandle				fLog;
	
	public SVDBOpenProjectJob(SVDBProjectManager pmgr, IProject p) {
		super("Opening Project " + p.getName());
		fProjectMgr = pmgr;
		fProject = p;
		
		fLog = LogFactory.getLogHandle("SVDBOpenProjectJob");
	}
	
	public void projectBuildStarted(IProject p) {
		if (fProject != null && p.equals(fProject)) {
			fProject = null;
		}
	}
	
	
	@Override
	public IStatus run(IProgressMonitor monitor) {
		if (fProject == null) {
			return Status.OK_STATUS;
		}

		fProjectMgr.startDelayedBuild(this);
		
		if (SVDBProjectManager.isSveProject(fProject)) {
			// Ensure the project nature is associated
			SVProjectNature.ensureHasSvProjectNature(fProject);
			
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			monitor.beginTask("Opening SV Project " + fProject.getName(), 1000);
			/** SVDBProjectData pdata = */ pmgr.getProjectData(fProject);
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
