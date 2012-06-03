package net.sf.sveditor.core.tests.job_mgr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.job_mgr.IJob;
import net.sf.sveditor.core.job_mgr.JobMgr;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class JobMgrTests extends TestCase {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("JobMgrTests");
		s.addTest(new TestSuite(JobMgrTests.class));
		return s;
	}
	
	public void testBasics() {
		JobMgr mgr = new JobMgr();
		List<IJob> jobs = new ArrayList<IJob>();
		final List<String> finished = new ArrayList<String>();
		
		for (int i=0; i<4; i++) {
			IJob job = mgr.createJob();
			job.init("Job " + i, new Runnable() {
				public void run() {
					synchronized (finished) {
						System.out.println("Job");
						finished.add("Job");
					}
				}
			});
			mgr.queueJob(job);
		}
		
		/*
		synchronized (jobs) {
			for (IJob j : jobs) {
				j.join();
			}
		}
		 */
		
		mgr.dispose();
		System.out.println("Done");
	}

}
