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
package org.eclipse.hdt.sveditor.core.db.project;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

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
			if (!monitor.isCanceled()) {
				schedule(fRetryInterval);
			}
		} else {
			fJob.schedule(fScheduleDelay);
		}
		
		return Status.OK_STATUS;
	}
	
	public static boolean isRefreshRunning() {
		LogHandle log = null;
		IJobManager job_mgr = Job.getJobManager();
		Job jobs[] = job_mgr.find(null);
		boolean found = false;

		for (Job j : jobs) {
			String name = j.getName();
			if (name.startsWith("Refresh") &&
					!name.contains("view")) {
				if (log == null) {
					log = LogFactory.getLogHandle("SVDBRefreshDoneJobWrapper");
				}
				log.debug("Refresh Job: " + j.getName());
				found = true;
//				break;
			}
		}

		return found;
	}

}
