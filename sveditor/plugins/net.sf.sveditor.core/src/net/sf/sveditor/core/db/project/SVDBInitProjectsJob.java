package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
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
			if (p.isOpen()) {
				if (SVDBProjectManager.isSveProject(p)) {
					sv_projects.add(p);
				}
			}
		}
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();

		monitor.beginTask("Initializing SV Projects", 1000*sv_projects.size());
	
		try {
			
			for (IProject p : sv_projects) {
				// Ensure that this project has the SV nature
				SVProjectNature.ensureHasSvProjectNature(p);
				
				monitor.subTask("Initializing " + p.getName());
				try {
					SVDBProjectData pdata = pmgr.getProjectData(p);
					// Getting the index collection causes the indexes 
					// to be initialized
					SVDBIndexCollection index_mgr = pdata.getProjectIndexMgr();
				} catch (Exception e) {
					// TODO: Log
					e.printStackTrace();
				}
				monitor.worked(1000);
			}
		} finally {
			monitor.done();
		}

		return Status.OK_STATUS;
	}

}
