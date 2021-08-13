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
package org.sveditor.core.tests.job_mgr;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.job_mgr.IJob;
import org.sveditor.core.job_mgr.JobMgr;

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
