package net.sf.sveditor.core.db.project;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBRemoveProjectJob extends Job {
	private SVDBProjectData				fProjectData;
	
	public SVDBRemoveProjectJob(SVDBProjectData pdata) {
		super("Removing Project " + pdata.getName());
		fProjectData = pdata;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		List<ISVDBIndex> index_list = fProjectData.getProjectIndexMgr().getIndexList();
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		monitor.beginTask("Close Project " + fProjectData.getName(), 
				1000*index_list.size());
		
		monitor.done();
		for (ISVDBIndex index : index_list) {
			monitor.subTask("Closing " + index.getBaseLocation());
			rgy.disposeIndex(index, "Project Closing");
		}
		
		return Status.OK_STATUS;
	}

}
