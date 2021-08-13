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
package org.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexOperation;
import org.sveditor.core.db.index.ISVDBIndexOperationRunner;
import org.sveditor.core.db.index.SVDBDeclCacheItem;

public class SVDBFindOperation implements ISVDBIndexOperation {
	private List<SVDBDeclCacheItem>				fResult;
	private String								fName;
	private ISVDBFindNameMatcher				fMatcher;
	
	public SVDBFindOperation() {
		fResult = new ArrayList<SVDBDeclCacheItem>();
	}

	static List<SVDBDeclCacheItem> find(
			IProgressMonitor			monitor,
			ISVDBIndexOperationRunner 	runner, 
			String						name,
			ISVDBFindNameMatcher		matcher,
			boolean						sync) {
		SVDBFindOperation op = new SVDBFindOperation();
		
		runner.execOp(monitor, op, sync);
		
		return op.fResult;
	}

	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(monitor, fName, fMatcher);
		fResult.addAll(result);
	}

}
