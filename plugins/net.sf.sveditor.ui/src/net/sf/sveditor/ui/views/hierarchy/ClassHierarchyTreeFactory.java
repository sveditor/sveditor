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


package net.sf.sveditor.ui.views.hierarchy;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class ClassHierarchyTreeFactory {
	private ISVDBIndexIterator				fIndexIt;
	
	public ClassHierarchyTreeFactory(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}
	
	public HierarchyTreeNode build(SVDBModIfcClassDecl cls) {
		Map<String, HierarchyTreeNode> class_map = 
			new HashMap<String, HierarchyTreeNode>();
		
		// Don't yet know if this class has a super
		HierarchyTreeNode ret = new HierarchyTreeNode(null, cls.getName());
		class_map.put(cls.getName(), ret);
		
		// Now, iterate through all classes in the index and build
		// the extension hierarchy
		ISVDBItemIterator<SVDBItem> it = fIndexIt.getItemIterator();
		while (it.hasNext()) {
			SVDBItem it_t = it.nextItem();
			if (it_t.getType() == SVDBItemType.Class) {
				SVDBModIfcClassDecl cls_t = (SVDBModIfcClassDecl)it_t;
				
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
						!cls_t.getSuperClass().equals("")) {
					// Create a speculative hierarchy node
					if (!class_map.containsKey(cls_t.getSuperClass())) {
						// Create a new node
						class_map.put(cls_t.getSuperClass(),
								new HierarchyTreeNode(null, cls_t.getSuperClass()));
					}
					
					cls_n.setParent(class_map.get(cls_t.getSuperClass()));
					class_map.get(cls_t.getSuperClass()).addChild(cls_n);
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
