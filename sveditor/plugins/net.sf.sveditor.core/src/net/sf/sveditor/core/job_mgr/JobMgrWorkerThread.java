package net.sf.sveditor.core.job_mgr;

import org.eclipse.core.runtime.NullProgressMonitor;

public class JobMgrWorkerThread extends Thread {
	
	public enum ThreadState {
		Waiting,
		Working
	};
	
	private ThreadState				fState;
	private int					fIdleTimeout = 1000;
	private JobMgr					fJobMgr;
	
	public JobMgrWorkerThread(JobMgr mgr) {
		super("JobMgrWorkerThread");
		fJobMgr = mgr;
	}
	
	public synchronized ThreadState getThreadState() {
		return fState;
	}

	@Override
	public void run() {
		// Wait for a job to become available
		while (true) {
			IJob job = fJobMgr.dequeueJob(fIdleTimeout);

			if (job != null) {
				job.run(new NullProgressMonitor());
				
				// Run the job
				fJobMgr.jobEnded(job);
			} else {
				if (fJobMgr.tryToExit(this)) {
					break;
				}
			}
		}
	}
	
	

}
