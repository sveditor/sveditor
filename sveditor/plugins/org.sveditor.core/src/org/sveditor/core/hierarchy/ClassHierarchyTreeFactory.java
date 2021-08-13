/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.sveditor.core.hierarchy;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.index.ops.SVDBFindClassExtensionsOp;
import org.sveditor.core.db.search.SVDBFindSuperClass;

public class ClassHierarchyTreeFactory {
	private ISVDBIndexIterator				fIndexIt;
	
	public ClassHierarchyTreeFactory(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}

	public HierarchyTreeNode build(SVDBDeclCacheItem cls) {
		return build((SVDBClassDecl)cls.getSVDBItem());
	}
	
	/**
	 * Returns: target hierarchy node
	 * 
	 * @param cls
	 * @return
	 */
	public HierarchyTreeNode build(SVDBClassDecl cls) {
		
		// Don't yet know if this class has a super
		HierarchyTreeNode target = new HierarchyTreeNode(null, cls.getName(), cls);
		HierarchyTreeNode root = target;
	
		// First, search up looking for super-classes
		SVDBFindSuperClass super_finder = new SVDBFindSuperClass(fIndexIt);
		SVDBClassDecl cls_t = cls, super_c;
		while ((super_c = super_finder.find(cls_t)) != null) {
			HierarchyTreeNode old_root = root;
			root = new HierarchyTreeNode(null, super_c.getName(), super_c);
			old_root.setParent(root);
			root.addChild(old_root);

			cls_t = super_c;
		}
		
		// Now, build down the hierarchy
		try {
			build_sub(target);
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return target;
	}
	
	private void build_sub(HierarchyTreeNode parent) {
		if (parent.getItemDecl().getType() != SVDBItemType.ClassDecl) {
			return;
		}
		
		List<SVDBDeclCacheItem> sub_classes = SVDBFindClassExtensionsOp.execOp(
				new NullProgressMonitor(), fIndexIt, (SVDBClassDecl)parent.getItemDecl());
		
		for (SVDBDeclCacheItem s : sub_classes) {
			if (s.getSVDBItem() instanceof SVDBClassDecl) {
				HierarchyTreeNode sn = new HierarchyTreeNode(
						parent, s.getName(), (SVDBClassDecl)s.getSVDBItem());
				parent.addChild(sn);
				build_sub(sn);
			}
		}
	}

}
