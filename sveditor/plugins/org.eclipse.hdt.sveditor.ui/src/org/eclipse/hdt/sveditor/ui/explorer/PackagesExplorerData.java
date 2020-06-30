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
package org.eclipse.hdt.sveditor.ui.explorer;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByTypeMatcher;

public class PackagesExplorerData extends DeferredProjectDataProvider {

	public PackagesExplorerData(IProjectPathsData p) {
		super(p, "Packages");
	}

	public Object[] getChildrenDeferred(Object parent) {
		IProjectPathsData p = (IProjectPathsData)parent;
		while (p.getParent(p) != null) {
			p = (IProjectPathsData)p.getParent(p);
		}
		ISVDBIndexIterator index_it = ((ProjectPathsData)p).getIndexIt();

		List<SVDBDeclCacheItem> packages = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), "",
				new SVDBFindByTypeMatcher(SVDBItemType.PackageDecl));		

		DeclCacheItem children[] = new DeclCacheItem[packages.size()];
		for (int i=0; i<packages.size(); i++) {
			children[i] = new DeclCacheItem(this, packages.get(i));
		}
		
		return children;
	}


}
