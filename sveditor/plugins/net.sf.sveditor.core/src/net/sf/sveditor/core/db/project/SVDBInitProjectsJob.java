package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ISVProjectDelayedOp;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRefresh;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;

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
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();

	
		try {
			subMonitor.beginTask("Initializing SV Projects", 1000*sv_projects.size());
			for (IProject p : sv_projects) {
				// Ensure that this project has the SV nature
				SVProjectNature.ensureHasSvProjectNature(p);
				SubMonitor proj_loopMonitor = subMonitor.newChild(1000);
				proj_loopMonitor.beginTask("Initalizing " + p.getName(), 1000);
				
				try {
					SVDBProjectData pdata = pmgr.getProjectData(p);
					// Getting the index collection causes the indexes 
					// to be initialized
					SVDBIndexCollection index_mgr = pdata.getProjectIndexMgr();

					List<ISVDBIndex> index_list = index_mgr.getIndexList();
					
					synchronized (index_list) {
						SubMonitor list_loopMonitor = proj_loopMonitor.newChild(1000);
						list_loopMonitor.setWorkRemaining(index_list.size()*1000);
						for (ISVDBIndex index : index_list) {
							SVDBIndexChangePlanRefresh refresh = new SVDBIndexChangePlanRefresh(index);
							index.execIndexChangePlan(list_loopMonitor.newChild(500), refresh);
							
							ISVDBIndexChangePlan plan = index.createIndexChangePlan(null);
							
							if (plan != null && plan.getType() != SVDBIndexChangePlanType.Empty) {
								index.execIndexChangePlan(list_loopMonitor.newChild(500), plan);
							} else{
								list_loopMonitor.worked(500);
							}
						}
					}
				} catch (Exception e) {
					// TODO: Log
					e.printStackTrace();
				}
			}
		} finally {
			subMonitor.done();
		}

		return Status.OK_STATUS;
	}

}
