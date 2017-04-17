/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.hierarchy;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class ModuleHierarchyTreeFactory {
	private ISVDBIndexIterator				fIndexIt;
	private SVDBFindByName					fFinder;
	private LogHandle						fLog;
	
	public ModuleHierarchyTreeFactory(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
		fFinder = new SVDBFindByName(fIndexIt);
		fLog = LogFactory.getLogHandle("ModuleHierarchyTreeFactory");
	}
	
	public HierarchyTreeNode build(SVDBDeclCacheItem mod) {
		return build((SVDBModIfcDecl)mod.getSVDBItem());
	}
	
	public HierarchyTreeNode build(SVDBModIfcDecl mod) {
		return build_s(null, mod, null);
	}
	
	private HierarchyTreeNode build_s(HierarchyTreeNode parent, SVDBModIfcDecl mod, SVDBModIfcInstItem inst_item) {
		HierarchyTreeNode ret;
		if (inst_item != null) {
			// Instance in the tree
			ret = new HierarchyTreeNode(parent, inst_item.getName(), inst_item, mod);
		} else {
			// Root of the tree
			ret = new HierarchyTreeNode(parent, mod.getName(), mod);
		}
		
		for (ISVDBItemBase it : mod.getChildren()) {
			if (it.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInst inst = (SVDBModIfcInst)it;
				if (inst.getTypeInfo() == null) {
					fLog.error("module instance \"" + inst.getName() + "\" has null type");
				}
				List<ISVDBItemBase> it_l = fFinder.findItems(inst.getTypeInfo().getName(), 
						SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl);
			
				for (SVDBModIfcInstItem inst_i : inst.getInstList()) {
					if (it_l.size() > 0) {
						HierarchyTreeNode n = build_s(ret, (SVDBModIfcDecl)it_l.get(0), inst_i);
						n.setItemDecl(inst_i);
						ret.addChild(n);
					} else if (it instanceof ISVDBNamedItem) {
						// ERROR: Unknown module
						fLog.error("Unknown module type " + it.getType() + " " + SVDBItem.getName(it));
						ret.addChild(new HierarchyTreeNode(ret, ((ISVDBNamedItem)it).getName()));
					}
				}
			}
		}
		
		return ret;
	}

}
