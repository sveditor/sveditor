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
package org.sveditor.ui.explorer;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.search.SVDBFindByTypeMatcher;

public class ClassesExplorerData extends DeferredProjectDataProvider {
	
	public ClassesExplorerData(IProjectPathsData p) {
		super(p, "Classes");
	}

	@Override
	public Object[] getChildrenDeferred(Object parent) {
		IProjectPathsData p = (IProjectPathsData)parent;
		while (p.getParent(p) != null) {
			p = (IProjectPathsData)p.getParent(p);
		}
		ISVDBIndexIterator index_it = ((ProjectPathsData)p).getIndexIt();

		List<SVDBDeclCacheItem> classes = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), "",
				new SVDBFindByTypeMatcher(SVDBItemType.ClassDecl));		

		DeclCacheItem children[] = new DeclCacheItem[classes.size()];
		for (int i=0; i<classes.size(); i++) {
			children[i] = new DeclCacheItem(this, classes.get(i));
		}
		
		return children;		
	}

}
