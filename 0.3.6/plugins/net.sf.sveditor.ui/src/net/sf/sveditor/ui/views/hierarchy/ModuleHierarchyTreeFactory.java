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

import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindByName;

public class ModuleHierarchyTreeFactory {
	private ISVDBIndexIterator				fIndexIt;
	private SVDBFindByName					fFinder;
	
	public ModuleHierarchyTreeFactory(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
		fFinder = new SVDBFindByName(fIndexIt);
	}
	
	public HierarchyTreeNode build(SVDBModIfcClassDecl mod) {
		return build_s(null, mod);
	}
	
	private HierarchyTreeNode build_s(HierarchyTreeNode parent, SVDBModIfcClassDecl mod) {
		HierarchyTreeNode ret = new HierarchyTreeNode(parent, mod.getName(), mod);
		
		for (SVDBItem it : mod.getItems()) {
			if (it.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInstItem inst = (SVDBModIfcInstItem)it;
				if (inst.getTypeInfo() == null) {
					System.out.println("module instance \"" + inst.getName() + "\" has null type");
				}
				List<SVDBItem> it_l = fFinder.find(inst.getTypeInfo().getName(), 
						SVDBItemType.Module, SVDBItemType.Interface);
				
				if (it_l.size() > 0) {
					HierarchyTreeNode n = build_s(ret, (SVDBModIfcClassDecl)it_l.get(0));
					n.setItemDecl(inst);
					ret.addChild(n);
				} else {
					// ERROR: Unknown module
					ret.addChild(new HierarchyTreeNode(ret, it.getName()));
				}
			}
		}
		
		return ret;
	}

}
