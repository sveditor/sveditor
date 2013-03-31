package net.sf.sveditor.core.db.index.builder;

import java.util.ArrayList;
import java.util.List;

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
	
		System.out.println("Schedule job for " + plan.getPlanner());
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
		
	}
	
	void notify_job_complete(SVDBIndexBuildJob job) {
		synchronized (fJobList) {
			fJobList.remove(job);
		}
	}

}
