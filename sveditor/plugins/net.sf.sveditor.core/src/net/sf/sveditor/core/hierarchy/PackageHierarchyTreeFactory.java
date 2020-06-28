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
package net.sf.sveditor.core.hierarchy;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;

public class PackageHierarchyTreeFactory {
	private ISVDBIndexIterator			fIndexIt;
	
	public PackageHierarchyTreeFactory(ISVDBIndexIterator it) {
		fIndexIt = it;
	}
	
	private static final Set<SVDBItemType>		fIncludedRootTypes;
	
	static {
		fIncludedRootTypes = new HashSet<SVDBItemType>();
		fIncludedRootTypes.add(SVDBItemType.TypeInfoEnum);
		fIncludedRootTypes.add(SVDBItemType.TypedefStmt);
		fIncludedRootTypes.add(SVDBItemType.ClassDecl);
		fIncludedRootTypes.add(SVDBItemType.VarDeclStmt);
	}

	public HierarchyTreeNode build(SVDBDeclCacheItem pkg) {
		HierarchyTreeNode root = new HierarchyTreeNode(
				null, pkg.getName(), pkg.getSVDBItem(), pkg);
	
		List<SVDBDeclCacheItem> contents = fIndexIt.findPackageDecl(
				new NullProgressMonitor(), pkg);
		
		
		for (SVDBDeclCacheItem c : contents) {
			if (c.getType() == SVDBItemType.ImportStmt) {
				List<String> pkg_list = new ArrayList<String>();
				buildImportHierarchy(pkg_list, root, c);
			}
		}
	
		return root;
	}
	
	private void buildImportHierarchy(
			List<String>		pkg_list,
			HierarchyTreeNode	parent,
			SVDBDeclCacheItem	imp_s) {
	
		int idx;
		String imp_path = imp_s.getName();
		if ((idx=imp_path.indexOf("::")) != -1) {
			imp_path = imp_path.substring(0, idx);
		}

		// Now, find the referenced package
		List<SVDBDeclCacheItem> pkg = fIndexIt.findGlobalScopeDecl(
				new NullProgressMonitor(), imp_path, 
				new SVDBFindByNameMatcher(SVDBItemType.PackageDecl));

		SVDBDeclCacheItem alt_i = (pkg.size()>0)?pkg.get(0):null;

		HierarchyTreeNode child = new HierarchyTreeNode(
				parent, imp_path, imp_s.getSVDBItem(), alt_i);
		parent.addChild(child);
		
		if (!pkg_list.contains(imp_path) && pkg.size() != 0) {
			int size = pkg_list.size();
			// Recurse and add sub-items
			List<SVDBDeclCacheItem> pkg_items = fIndexIt.findPackageDecl(
					new NullProgressMonitor(), pkg.get(0));
			for (SVDBDeclCacheItem si : pkg_items) {
				if (si.getType() == SVDBItemType.ImportStmt) {
					buildImportHierarchy(pkg_list, child, si);
				}
			}
			// Resize back to the previous size
			while (pkg_list.size() > size) {
				pkg_list.remove(pkg_list.size()-1);
			}
		}
	}
}
