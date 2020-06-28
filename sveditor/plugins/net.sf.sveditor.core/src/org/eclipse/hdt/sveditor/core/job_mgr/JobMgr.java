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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.job_mgr.JobMgrWorkerThread.ThreadState;

public class JobMgr implements IJobMgr {
	
	private List<IJobListener>			fJobListeners;
	private List<JobMgrWorkerThread>	fThreadPool;
	private List<IJob>					fJobQueue;
	private int						fMaxThreads;
	private boolean					fDisposed;
	
	public JobMgr() {
		fJobListeners = new ArrayList<IJobListener>();
		fThreadPool = new ArrayList<JobMgrWorkerThread>();
		fJobQueue = new ArrayList<IJob>();
		
		fMaxThreads = 4;
	}
	
	public void dispose() {
		fDisposed = true;
		
		// Wait for all the threads to exit
		synchronized (fThreadPool) {
			while (fThreadPool.size() > 0) {
				try {
					fThreadPool.wait();
				} catch (InterruptedException e) {
					break;
				}
			}
		}
	}
	
	public void addJobListener(IJobListener l) {
		synchronized (fJobListeners) {
			fJobListeners.add(l);
		}
	}

	public void removeJobListener(IJobListener l) {
		synchronized (fJobListeners) {
			fJobListeners.remove(l);
		}
	}
	
	public IJob createJob() {
		return new JobMgrJob();
	}

	public void queueJob(IJob job) {
		checkWorkerThreads();
		synchronized (fJobQueue) {
			// Find an insertion point such that we preserve priority order
			if (fJobQueue.size() == 0 || 
					fJobQueue.get(fJobQueue.size()-1).getPriority() <= job.getPriority()) {
				fJobQueue.add(job);
			} else {
				boolean added = false;
				for (int i=0; i<fJobQueue.size(); i++) {
					if (fJobQueue.get(i).getPriority() > job.getPriority()) {
						fJobQueue.add(i, job);
						added = true;
						break;
					}
				}
				if (!added) {
					fJobQueue.add(job);
				}
			}
			fJobQueue.notifyAll();
		}
	}

	/**
	 * Check to see if we should launch a new thread
	 */
	private void checkWorkerThreads() {
		synchronized (fThreadPool) {
			boolean all_busy = true;
			for (JobMgrWorkerThread t : fThreadPool) {
				if (t.getThreadState() == ThreadState.Waiting) {
					all_busy = false;
				}
			}
			if (all_busy && fThreadPool.size() < fMaxThreads) {
				JobMgrWorkerThread t = new JobMgrWorkerThread(this);
				fThreadPool.add(t);
				t.start();
			}
		}
	}
	
	public IJob dequeueJob(int idle_timeout) {
		IJob job = null;
		for (int i=0; i<2; i++) {
			synchronized (fJobQueue) {
				if (fJobQueue.size() > 0) {
					job = fJobQueue.remove(0);
					break;
				} else if (i == 0) {
					// Wait for a bit
					try {
						fJobQueue.wait(idle_timeout);
					} catch (InterruptedException e) {}
				}
			}
		}
		
		if (job != null) {
			jobStarted(job);
		}
		
		return job;
	}
	
	private void jobStarted(IJob job) {
		synchronized (fJobListeners) {
			for (IJobListener l : fJobListeners) {
				l.jobStarted(job);
			}
		}
	}

	void jobEnded(IJob job) {
		synchronized (fJobListeners) {
			for (IJobListener l : fJobListeners) {
				l.jobEnded(job);
			}
		}
	}

	/**
	 * Called by the worker thread to see if it can exit
	 * 
	 * @param t
	 * @return
	 */
	public boolean tryToExit(JobMgrWorkerThread t) {
		boolean can_exit = true;
		synchronized (fThreadPool) {
			can_exit = (fThreadPool.size() > 1 || fDisposed);
			if (can_exit) {
				fThreadPool.remove(t);
				fThreadPool.notifyAll();
			}
		}
		return can_exit;
	}
}
