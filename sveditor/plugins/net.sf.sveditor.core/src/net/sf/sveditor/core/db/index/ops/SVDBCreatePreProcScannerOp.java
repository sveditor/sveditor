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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;
import net.sf.sveditor.core.preproc.ISVPreProcessor;

public class SVDBCreatePreProcScannerOp implements ISVDBIndexOperation {
	private String					fPath;
	private ISVPreProcessor			fPreProc;
	
	public SVDBCreatePreProcScannerOp(String path) {
		fPath = path;
		fPreProc = null;
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		ISVDBIndexInt index_int = (ISVDBIndexInt)index;
		
		fPreProc = index_int.createPreProcScanner(fPath);
	}
	
	public static ISVPreProcessor op(ISVDBIndexOperationRunner runner, String path) {
		SVDBCreatePreProcScannerOp op = new SVDBCreatePreProcScannerOp(path);
		runner.execOp(new NullProgressMonitor(), op, true);
		
		return op.fPreProc;
	}

}
