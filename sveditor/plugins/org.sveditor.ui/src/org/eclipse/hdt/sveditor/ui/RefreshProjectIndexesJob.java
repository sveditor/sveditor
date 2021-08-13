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
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;

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
					if (!(i instanceof SVDBArgFileIndex)) {
						index_list_1.add(i);
					}
				}
				if (SVUiPlugin.getDefault() != null) {
					SVUiPlugin.getDefault().refreshIndexList(index_list_1);
				}
			}
		}

		return Status.OK_STATUS;
	}

}
