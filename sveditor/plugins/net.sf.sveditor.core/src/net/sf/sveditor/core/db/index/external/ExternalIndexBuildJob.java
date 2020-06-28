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
package net.sf.sveditor.core.db.index.external;

import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;

public class ExternalIndexBuildJob extends Thread implements ISVDBIndexBuildJob {

	private IProgressMonitor				fMonitor;
	private ExternalIndexBuilder			fBuilder;
	private ISVDBIndexChangePlan			fPlan;
	private boolean							fIsStarted;
	private boolean							fIsDone;
	private Object							fSyncObj;
	
	ExternalIndexBuildJob(ExternalIndexBuilder builder, ISVDBIndexChangePlan plan) {
		fBuilder = builder;
		fPlan = plan;
	}

	@Override
	public ISVDBIndexChangePlan getPlan() {
		return fPlan;
	}

	@Override
	public void waitComplete() {
		boolean is_done = false;
		while (!is_done) {
			synchronized (fSyncObj) {
				is_done = fIsDone;
			}
			
			if (!is_done) {
				synchronized (fSyncObj) {
					try {
						fSyncObj.wait();
					} catch (InterruptedException e) {
						e.printStackTrace();
						break;
					}
				}
			}
		}
	}

	@Override
	public synchronized boolean canReplace(ISVDBIndexChangePlan plan) {
		return (!fIsStarted && plan.equals(fPlan));
	}

	@Override
	public void run() {
		Exception ex = null;
		
		synchronized (this) {
			fIsStarted = true;
		}
		
		System.out.println("ExternalIndexBuildJob: run");
		
		try {
			fPlan.getPlanner().execIndexChangePlan(fMonitor, fPlan);
		} catch (Exception e) {
			e.printStackTrace();
			ex = e;
		}
		
		synchronized (fSyncObj) {
			fBuilder.notify_job_complete(this);
			fIsDone = true;
			fSyncObj.notifyAll();
		}
	}
	

}
