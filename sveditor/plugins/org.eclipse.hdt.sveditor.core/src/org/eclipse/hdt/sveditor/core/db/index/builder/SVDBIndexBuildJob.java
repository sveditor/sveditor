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
package org.eclipse.hdt.sveditor.core.db.index.builder;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBIndexBuildJob extends Job implements ISVDBIndexBuildJob {
	private SVDBIndexBuilder					fIndexBuilder;
	private ISVDBIndexChangePlan				fPlan;
	private Object								fSyncObj;
	private boolean								fIsStarted;
	private boolean								fIsDone;

	/**
	 * Build Jobs are only created by the build manager
	 * 
	 * @param index_builder
	 * @param plan
	 */
	SVDBIndexBuildJob(
			SVDBIndexBuilder		index_builder,
			ISVDBIndexChangePlan 	plan) {
		super("SVDBIndexBuildJob");
		fIndexBuilder = index_builder;
		fPlan = plan;
		fSyncObj = new Object();
	}
	
	public ISVDBIndexChangePlan getPlan() {
		return fPlan;
	}
	
	public synchronized boolean canReplace(ISVDBIndexChangePlan plan) {
		return (!fIsStarted && plan.equals(fPlan));
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		Exception ex = null;
		synchronized (this) {
			fIsStarted = true;
		}
		
		try {
			fPlan.getPlanner().execIndexChangePlan(monitor, fPlan);
		} catch (Exception e) {
			e.printStackTrace();
			ex = e;
		} finally {
			synchronized (this) {
				fIsDone = true;
			}
			
			synchronized (fSyncObj) {
				fIndexBuilder.notify_job_complete(this);
				fIsDone = true;
				fSyncObj.notifyAll();
			} 
			
			if (ex == null) {
				// Try a replan
				if (fPlan.getType() == SVDBIndexChangePlanType.Refresh) {
					ISVDBIndexChangePlan plan = fPlan.getPlanner().createIndexChangePlan(null);
					if (plan.getType() != SVDBIndexChangePlanType.Empty) {
						fIndexBuilder.build(plan);
					}
				}
			}
		}
		
		return Status.OK_STATUS;
	}

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
}
