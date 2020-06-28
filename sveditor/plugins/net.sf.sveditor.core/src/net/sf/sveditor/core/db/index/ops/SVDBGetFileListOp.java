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

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBGetFileListOp implements ISVDBIndexOperation {
	private List<String>				fFileList;
	
	public SVDBGetFileListOp() {
		fFileList = new ArrayList<String>();
	}
	
	public List<String> getFileList() {
		return fFileList;
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		for (String path : index.getFileList(new NullProgressMonitor())) {
			fFileList.add(path);
		}
	}
	
	public static List<String> op(ISVDBIndex index, boolean sync) {
		SVDBGetFileListOp op = new SVDBGetFileListOp();

		index.execOp(new NullProgressMonitor(), op, sync);
		
		return op.getFileList();
	}

}
