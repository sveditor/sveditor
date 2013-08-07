package net.sf.sveditor.core.db.project;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;

/**
 * This class is a bit of a hack, but does seem to work.
 * The goal, here, is to ensure that the target job only
 * is scheduled and run once the pending refresh job is complete
 * @author ballance
 *
 */
public class SVDBRefreshDoneJobWrapper extends Job {
	private int						fRetryInterval = 1000;
	private Job						fJob;
	private int						fScheduleDelay;
	
	public SVDBRefreshDoneJobWrapper(Job j, int schedule_delay) {
		super("Wait for Refresh Complete");
		fJob = j;
		fScheduleDelay = schedule_delay;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {

		if (isRefreshRunning()) {
			SVDBRefreshDoneJobWrapper jw = new SVDBRefreshDoneJobWrapper(fJob, fScheduleDelay);
			jw.schedule(fRetryInterval);
		} else {
			fJob.schedule(fScheduleDelay);
		}
		
		return Status.OK_STATUS;
	}
	
	public static boolean isRefreshRunning() {
		IJobManager job_mgr = Job.getJobManager();
		Job jobs[] = job_mgr.find(null);
		boolean found = false;

		for (Job j : jobs) {
			if (j.getName().startsWith("Refresh")) {
				found = true;
				break;
			}
		}

		return found;
	}

}
