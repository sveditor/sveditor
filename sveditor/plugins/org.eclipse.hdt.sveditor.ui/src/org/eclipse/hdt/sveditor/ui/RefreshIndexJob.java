/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class RefreshIndexJob extends Job implements ILogLevel {
	private List<ISVDBIndex>			fIndexRebuildList;
	private SVUiPlugin					fParent;
	private LogHandle					fLog;
	
	public RefreshIndexJob(SVUiPlugin parent) {
		super("Refresh Index");
		fIndexRebuildList = new ArrayList<ISVDBIndex>();
		fParent = parent;
		fLog = LogFactory.getLogHandle("RefreshIndexJob");
	}
	
	public void addIndex(ISVDBIndex index) {
		synchronized (fIndexRebuildList) {
			fIndexRebuildList.add(index);
		}
	}
	
	public void addIndexList(List<ISVDBIndex> list) {
		synchronized (fIndexRebuildList) {
			fIndexRebuildList.addAll(list);
		}
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		synchronized (fIndexRebuildList) {
			subMonitor.beginTask("Refreshing Indexes", 20*fIndexRebuildList.size());
		}
		long rebuild_start_time;
		long task_start_time;
		String projects = new String();
		rebuild_start_time = System.currentTimeMillis();
		while (true) {
			ISVDBIndex index = null;
			synchronized (fIndexRebuildList) {
				if (fIndexRebuildList.size() == 0) {
					break;
				} else {
					index = fIndexRebuildList.remove(0);
					projects += index.getProject() + " ";
				}
			}
		
			try {
				task_start_time = System.currentTimeMillis();
				// Skew monitor the weights of these two tasks a bit so that they are somewhat time related
				index.rebuildIndex(subMonitor.newChild(5));
				fLog.debug(LEVEL_MID, "RefreshIndexJob - " + index.getProject() + " " + index.getBaseLocation() + ": rebuildIndex took " + (System.currentTimeMillis() - task_start_time)/1000 + " seconds");
				task_start_time = System.currentTimeMillis();
				index.loadIndex(subMonitor.newChild(15));
				fLog.debug(LEVEL_MID, "RefreshIndexJob - " + index.getProject() + " " + index.getBaseLocation() + ": loadIndex took " + (System.currentTimeMillis() - task_start_time)/1000 + " seconds");
			} catch (Exception e) {
				fLog.error("Exception during index refresh: " + e.getMessage(), e);
			}
		}
		
		subMonitor.done();
		fParent.refreshJobComplete();
		fLog.debug(LEVEL_MIN, "RefreshIndexJob: The entire rebuild for projects " + projects.toString() + " took " + (System.currentTimeMillis() - rebuild_start_time)/1000 + " seconds");
		
		return Status.OK_STATUS;
	}

}
