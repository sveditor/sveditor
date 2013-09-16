package net.sf.sveditor.core;

import net.sf.sveditor.core.db.index.ISVDBIndex;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;

public class SVMarkerPropagateJob extends Job {
	private ISVDBIndex				fIndex;
	
	public SVMarkerPropagateJob(ISVDBIndex index) {
		super("Propagate Markers: " + index.getBaseLocation());
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		return null;
	}

}
