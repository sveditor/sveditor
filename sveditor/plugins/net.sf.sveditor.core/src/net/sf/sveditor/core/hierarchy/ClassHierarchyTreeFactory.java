/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.hierarchy;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;

import org.eclipse.core.runtime.NullProgressMonitor;

public class ClassHierarchyTreeFactory {
	private ISVDBIndexIterator				fIndexIt;
	
	public ClassHierarchyTreeFactory(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}
	
	public HierarchyTreeNode build(SVDBClassDecl cls) {
		Map<String, HierarchyTreeNode> class_map = 
			new HashMap<String, HierarchyTreeNode>();
		
		// Don't yet know if this class has a super
		HierarchyTreeNode ret = new HierarchyTreeNode(null, cls.getName());
		class_map.put(cls.getName(), ret);
		
		// Now, iterate through all classes in the index and build
		// the extension hierarchy
		List<SVDBDeclCacheItem> cls_list = fIndexIt.findGlobalScopeDecl(
				new NullProgressMonitor(), "", new ISVDBFindNameMatcher() {
					public boolean match(ISVDBNamedItem it, String name) {
						return (it.getType() == SVDBItemType.ClassDecl);
					}
				});
		
		ISVDBItemIterator it = fIndexIt.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			ISVDBItemBase it_t = it.nextItem();
			if (it_t.getType() == SVDBItemType.ClassDecl) {
				SVDBClassDecl cls_t = (SVDBClassDecl)it_t;
				
				// Check for an empty super-node
				HierarchyTreeNode cls_n = null;
				if (class_map.containsKey(cls_t.getName())) {
					cls_n = class_map.get(cls_t.getName());
					cls_n.setItemDecl(cls_t);
				} else {
					cls_n = new HierarchyTreeNode(null, cls_t.getName(), cls_t);
					class_map.put(cls_t.getName(), cls_n);
				}
				
				if (cls_t.getSuperClass() != null && 
						cls_t.getSuperClass().getName() != null &&
						!cls_t.getSuperClass().getName().equals("")) {
					String super_cls_name = cls_t.getSuperClass().getName();
					// Create a speculative hierarchy node
					if (!class_map.containsKey(super_cls_name)) {
						// Create a new node
						class_map.put(super_cls_name,
								new HierarchyTreeNode(null, super_cls_name));
					}
					
					cls_n.setParent(class_map.get(super_cls_name));
					class_map.get(super_cls_name).addChild(cls_n);
				}
			}
		}
		
		// Iterate up the inheritance tree and prune any 
		// branches that are not related to the target class
		HierarchyTreeNode nt = ret, p;

		while ((p = nt.getParent()) != null) {
			for (int i=0; i<p.getChildren().size(); i++) {
				if (p.getChildren().get(i) != nt) {
					p.getChildren().remove(i);
					i--;
				}
			}
			nt = nt.getParent();
		}
		
		return ret;
	}

}
