package net.sf.sveditor.core.db.index.external;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlanner;

public class ExternalIndexBuilder implements ISVDBIndexBuilder {
	private List<ExternalIndexBuildJob>				fBuildQueue;
	private ExternalIndexBuildJob					fActiveJob;
	
	public ExternalIndexBuilder() {
		fBuildQueue = new ArrayList<ExternalIndexBuildJob>();
	}

	@Override
	public ISVDBIndexBuildJob build(ISVDBIndexChangePlan plan) {
		System.out.println("ExternalIndexBuilder: build");
		ExternalIndexBuildJob job = new ExternalIndexBuildJob(this, plan);
		synchronized (this) {
			if (fActiveJob == null) {
				fActiveJob = job;
				job.start();
			} else {
				// Queue job for later
				synchronized (fBuildQueue) {
					fBuildQueue.add(job);
				}
			}
		}
		
		return job;
	}

	@Override
	public ISVDBIndexBuildJob findJob(ISVDBIndexChangePlanner planner) {
		synchronized (this) {
			if (fActiveJob != null && fActiveJob.getPlan().getPlanner() == planner) {
				return fActiveJob;
			}
		}
	
		ExternalIndexBuildJob job = null;
		synchronized (fBuildQueue) {
			
			for (ExternalIndexBuildJob j : fBuildQueue) {
				if (j.getPlan().getPlanner() == planner) {
					job = j;
					break;
				}
			}
		}
		
		return job;
	}
	
	void notify_job_complete(ExternalIndexBuildJob job) {
	
		ExternalIndexBuildJob next = null;
		synchronized (fBuildQueue) {
			next = fBuildQueue.remove(0);
		}
		
		synchronized (this) {
			fActiveJob = next;
			
			if (next != null) {
				next.start();
			}
		}
	}
	

	// Wait for all jobs to be complete
	public void waitComplete() {
		
	}
}
