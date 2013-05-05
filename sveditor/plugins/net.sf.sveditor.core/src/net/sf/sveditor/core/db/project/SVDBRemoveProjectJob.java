package net.sf.sveditor.core.db.project;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBRemoveProjectJob extends Job {
	private SVDBProjectData				fProjectData;
	
	public SVDBRemoveProjectJob(SVDBProjectData pdata) {
		super("Removing Project " + pdata.getName());
		fProjectData = pdata;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		return null;
	}

}
