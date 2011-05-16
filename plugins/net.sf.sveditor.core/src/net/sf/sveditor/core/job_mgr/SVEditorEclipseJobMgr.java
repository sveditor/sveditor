package net.sf.sveditor.core.job_mgr;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVEditorEclipseJobMgr implements ISVEditorJobMgr {
	private Map<String, Queue<ISVEditorJob>>		fJobQueueMap;
	private Map<String, Job>						fJobMap;
	
	private class JobWrapper extends Job {
		private ISVEditorJob			fJob;
		
		public JobWrapper(ISVEditorJob job) {
			super(job.getName());
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			fJob.pre_run();
			try {
				fJob.run(monitor);
			} catch (SVJobException e) {
				e.printStackTrace();
			}
			fJob.post_run();
			
			synchronized (fJobMap) {
				fJobMap.remove(fJob.getKind());
				synchronized (fJobQueueMap) {
					for (Entry<String, Queue<ISVEditorJob>> e : fJobQueueMap.entrySet()) {
						if (!e.getValue().isEmpty() && !fJobMap.containsKey(e.getKey())) {
							ISVEditorJob job_t = e.getValue().remove();
							startJob(job_t);
						}
					}
				}
			}
			return Status.OK_STATUS;
		}
	}
	
	public SVEditorEclipseJobMgr() {
		fJobQueueMap = new HashMap<String, Queue<ISVEditorJob>>();
		fJobMap = new HashMap<String, Job>();
	}

	public void queueJob(ISVEditorJob job) {
		if (!fJobQueueMap.containsKey(job.getKind())) {
			fJobQueueMap.put(job.getKind(), new LinkedList<ISVEditorJob>());
		}
		
		synchronized (fJobQueueMap) {
			fJobQueueMap.get(job.getKind()).add(job);
		}
		
		synchronized (fJobMap) {
			if (!fJobMap.containsKey(job.getKind())) {
				synchronized (fJobQueueMap) {
					ISVEditorJob job_t = fJobQueueMap.get(job.getKind()).remove();
					startJob(job_t);
				}
			}
		}
	}
	
	private void startJob(ISVEditorJob job) {
		JobWrapper wrapper = new JobWrapper(job);
		
		wrapper.schedule();
	}
}
