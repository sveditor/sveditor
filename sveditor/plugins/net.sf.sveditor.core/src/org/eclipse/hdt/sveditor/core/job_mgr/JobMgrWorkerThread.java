/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.job_mgr;

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
				try {
					job.run(new NullProgressMonitor());
				} catch (Exception e) {
					e.printStackTrace();
				}
				
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
