package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBInitProjectsJob extends Job {
	
	public SVDBInitProjectsJob() {
		super("Init SV Projects");
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IProject projects[] = root.getProjects();
		
		List<IProject> sv_projects = new ArrayList<IProject>();

		for (IProject p : projects) {
			if (SVDBProjectManager.isSveProject(p)) {
				sv_projects.add(p);
			}
		}
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();

		monitor.beginTask("Initializing SV Projects", 1000*sv_projects.size());
	
		try {
			
			for (IProject p : sv_projects) {
				monitor.subTask("Initializing " + p.getName());
				try {
					SVDBProjectData pdata = pmgr.getProjectData(p);
				} catch (Exception e) {
					// TODO: Log
				}
				monitor.worked(1000);
			}
		} finally {
			monitor.done();
		}

		return Status.OK_STATUS;
	}

}
