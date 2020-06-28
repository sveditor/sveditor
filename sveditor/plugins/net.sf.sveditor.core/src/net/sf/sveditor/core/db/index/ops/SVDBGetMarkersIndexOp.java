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
package net.sf.sveditor.core.db.index.ops;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBGetMarkersIndexOp implements ISVDBIndexOperation {
	private List<SVDBMarker>				fMarkers;

	public SVDBGetMarkersIndexOp() {
		fMarkers = new ArrayList<SVDBMarker>();
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		Iterable<String> paths = index.getFileList(new NullProgressMonitor(), 
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_ARG_FILE+
				ISVDBDeclCache.FILE_ATTR_HAS_MARKERS);
		for (String path : paths) {
			if (monitor.isCanceled()) {
				break;
			}
			
			List<SVDBMarker> m_l = index.getMarkers(path);
			
			if (m_l != null && m_l.size() > 0) {
				for (SVDBMarker m : m_l) {
					fMarkers.add(m);
				}
			}
		}
	}
	
	public static List<SVDBMarker> op(ISVDBIndexOperationRunner runner, boolean sync) {
		SVDBGetMarkersIndexOp index_op = new SVDBGetMarkersIndexOp();
		
		runner.execOp(new NullProgressMonitor(), index_op, sync);
		
		return index_op.fMarkers;
	}

}
