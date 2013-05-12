package net.sf.sveditor.core.db.index.builder;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.jobs.Job;

public class SVDBIndexBuilder implements ISVDBIndexBuilder {
	private List<SVDBIndexBuildJob>			fJobList;
	
	public SVDBIndexBuilder() {
		fJobList = new ArrayList<SVDBIndexBuildJob>();
	}
	
	public SVDBIndexBuildJob build(ISVDBIndexChangePlan plan) {
		SVDBIndexBuildJob job = null;
		
		synchronized (fJobList) {
			for (SVDBIndexBuildJob j : fJobList) {
				if (j.canReplace(plan)) {
					job = j;
					break;
				}
			}
		}
		
		if (job == null) {
			job = new SVDBIndexBuildJob(this, plan);
			synchronized (fJobList) {
				fJobList.add(job);
			}
		}
	
		job.setPriority(Job.BUILD);
		job.schedule();
	
		return job;
	}
	
	public SVDBIndexBuildJob findJob(ISVDBIndexChangePlanner planner) {
		SVDBIndexBuildJob job = null;
		
		synchronized (fJobList) {
			for (SVDBIndexBuildJob j : fJobList) {
				if (j.getPlan().getPlanner() == planner) {
					job = j;
					break;
				}
			}
		}
		
		return job;
	}



	public void dispose() {
		while (true) {
			SVDBIndexBuildJob job = null;
			synchronized (fJobList) {
				if (fJobList.size() > 0) {
					job = fJobList.get(0);
				}
			}
			
			if (job != null) {
				job.waitComplete();
			} else {
				break;
			}
		}
	}
	
	void notify_job_complete(SVDBIndexBuildJob job) {
		synchronized (fJobList) {
			fJobList.remove(job);
		}
	}

}
