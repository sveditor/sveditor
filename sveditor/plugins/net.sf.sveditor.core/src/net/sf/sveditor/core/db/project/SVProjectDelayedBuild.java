package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;

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

}
