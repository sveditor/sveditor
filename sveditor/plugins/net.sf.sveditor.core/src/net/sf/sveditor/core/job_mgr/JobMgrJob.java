package net.sf.sveditor.core.job_mgr;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

public class JobMgrJob implements IJob {

	private List<IJobListener>		fJobListeners; 
	private String					fName;
	private Runnable				fRunnable;
	private Object					fJobDoneMutex;
	private boolean				fJobDone;

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

	public void run(IProgressMonitor monitor) {
		jobStarted();
		fRunnable.run();
		jobEnded();
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
}
