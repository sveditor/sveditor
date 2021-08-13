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
package org.sveditor.core.job_mgr;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

public class JobMgrJob implements IJob {

	private List<IJobListener>		fJobListeners; 
	private String					fName;
	private Runnable				fRunnable;
	private Object					fJobDoneMutex;
	private boolean				fJobDone;
	private int					fPriority = 5;

	public JobMgrJob() {
		fJobListeners = new ArrayList<IJobListener>();
		fJobDoneMutex = new Object();
	}
	
	public void init(String name, Runnable runnable) {
		fName = name;
		fRunnable = runnable;
		fJobDone = false;
	}

	public String getName() {
		return fName;
	}
	
	public void setPriority(int p) {
		fPriority = p;
	}
	
	public int getPriority() {
		return fPriority;
	}

	public void run(IProgressMonitor monitor) {
		try {
			jobStarted();
			fRunnable.run();
		} finally {
			jobEnded();
		}
	}
	
	private void jobStarted() {
		synchronized (fJobDoneMutex) {
			fJobDone = false;
		}
		synchronized (fJobListeners) {
			for (IJobListener l : fJobListeners) {
				l.jobStarted(this);
			}
		}
	}

	private void jobEnded() {
		synchronized (fJobDoneMutex) {
			fJobDone = true;
			fJobDoneMutex.notifyAll();
		}
		synchronized (fJobListeners) {
			for (IJobListener l : fJobListeners) {
				l.jobEnded(this);
			}
		}
	}
	
	public void addListener(IJobListener l) {
		synchronized (fJobListeners) {
			fJobListeners.add(l); 
		}
	}

	public void removeListener(IJobListener l) {
		synchronized (fJobListeners) {
			fJobListeners.remove(l);
		}
	}

	public void clearListeners() {
		synchronized (fJobListeners) {
			fJobListeners.clear();
		}
	}
	
	public void join() {
		synchronized (fJobDoneMutex) {
			while (!fJobDone) {
				try {
					fJobDoneMutex.wait();
				} catch (InterruptedException e) {
					break;
				}
			}
		}
	}
	
	public boolean join(int wait_ms) {
		boolean job_done = false;
		synchronized (fJobDoneMutex) {
			if (!fJobDone) {
				try {
					fJobDoneMutex.wait(wait_ms);
				} catch (InterruptedException e) { }
			}
			job_done = fJobDone;
		}
		return job_done;
	}
}
