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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class RefreshProjectIndexesJob extends Job {
	
	public RefreshProjectIndexesJob() {
		super("Refresh Project Indexes");
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		if (SVCorePlugin.getDefault() != null) {
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			
			for (SVDBProjectData p : mgr.getProjectList()) {
				List<ISVDBIndex> index_list = rgy.getProjectIndexList(p.getName());
			
				// Only rebuild non-'new' indexes
				List<ISVDBIndex> index_list_1 = new ArrayList<ISVDBIndex>();
				for (ISVDBIndex i : index_list) {
					if (!(i instanceof SVDBArgFileIndex2)) {
						index_list_1.add(i);
					}
				}
				SVUiPlugin.getDefault().refreshIndexList(index_list_1);
			}
		}

		return Status.OK_STATUS;
	}

}
