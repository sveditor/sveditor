package net.sf.sveditor.ui;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class RefreshProjectIndexesJob extends Job {
	
	public RefreshProjectIndexesJob() {
		super("Refresh Project Indexes");
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		for (SVDBProjectData p : mgr.getProjectList()) {
			List<ISVDBIndex> index_list = rgy.getProjectIndexList(p.getName());
			SVUiPlugin.getDefault().refreshIndexList(index_list);
		}
		
		return Status.OK_STATUS;
	}

}
