/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

public class RefreshIndexJob extends Job {
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
		synchronized (fIndexRebuildList) {
			monitor.beginTask("Refreshing Indexes", fIndexRebuildList.size());
		}
		
		while (true) {
			ISVDBIndex index = null;
			synchronized (fIndexRebuildList) {
				if (fIndexRebuildList.size() == 0) {
					break;
				} else {
					index = fIndexRebuildList.remove(0);
				}
			}
		
			try {
				SubProgressMonitor sub = new SubProgressMonitor(monitor, 1);
				index.loadIndex(sub);
				index.rebuildIndex();
			} catch (Exception e) {
				fLog.error("Exception during index refresh: " + e.getMessage(), e);
			}
		}
		monitor.done();
		fParent.refreshJobComplete();
		
		return Status.OK_STATUS;
	}

}
