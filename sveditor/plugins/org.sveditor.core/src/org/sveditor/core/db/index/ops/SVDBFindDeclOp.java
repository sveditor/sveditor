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
package org.sveditor.core.db.index.ops;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexOperation;
import org.sveditor.core.db.index.ISVDBIndexOperationRunner;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.search.ISVDBFindNameMatcher;

public class SVDBFindDeclOp implements ISVDBIndexOperation {
	private String								fName;
	private ISVDBFindNameMatcher				fMatcher;
	private List<SVDBDeclCacheItem>				fResults;
	
	public SVDBFindDeclOp(String name, ISVDBFindNameMatcher matcher) {
		fName = name;
		fMatcher = matcher;
		fResults = new ArrayList<SVDBDeclCacheItem>();
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(new NullProgressMonitor(), fName, fMatcher);
		
		fResults.addAll(result);
	}
	
	public static List<SVDBDeclCacheItem> op(ISVDBIndexOperationRunner runner, String name, ISVDBFindNameMatcher matcher, boolean sync) {
		SVDBFindDeclOp op = new SVDBFindDeclOp(name, matcher);
	
		runner.execOp(new NullProgressMonitor(), op, sync);

		return op.fResults;
	}

}
