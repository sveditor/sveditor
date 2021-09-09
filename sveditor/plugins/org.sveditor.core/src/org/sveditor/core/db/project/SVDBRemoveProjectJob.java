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
package org.sveditor.core.db.project;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.SVDBIndexRegistry;

public class SVDBRemoveProjectJob extends Job {
	private SVDBProjectData				fProjectData;
	
	public SVDBRemoveProjectJob(SVDBProjectData pdata) {
		super("Removing Project " + pdata.getName());
		fProjectData = pdata;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		List<ISVDBIndex> index_list = fProjectData.getProjectIndexMgr().getIndexList();
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Close Project " + fProjectData.getName(), 
				index_list.size());
		
		for (ISVDBIndex index : index_list) {
			subMonitor.subTask("Closing " + index.getBaseLocation());
			rgy.disposeIndex(index, "Project Closing");
			subMonitor.worked(1);
		}
		
		subMonitor.done();
		return Status.OK_STATUS;
	}

}
