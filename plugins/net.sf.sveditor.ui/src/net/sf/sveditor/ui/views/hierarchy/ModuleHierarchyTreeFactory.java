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

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
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
	
	public HierarchyTreeNode build(SVDBModIfcClassDecl mod) {
		return build_s(null, mod);
	}
	
	private HierarchyTreeNode build_s(HierarchyTreeNode parent, SVDBModIfcClassDecl mod) {
		HierarchyTreeNode ret = new HierarchyTreeNode(parent, mod.getName(), mod);
		
		for (ISVDBItemBase it : mod.getItems()) {
			if (it.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInstItem inst = (SVDBModIfcInstItem)it;
				if (inst.getTypeInfo() == null) {
					fLog.error("module instance \"" + inst.getName() + "\" has null type");
				}
				List<ISVDBItemBase> it_l = fFinder.find(inst.getTypeInfo().getName(), 
						SVDBItemType.Module, SVDBItemType.Interface);
				
				if (it_l.size() > 0) {
					HierarchyTreeNode n = build_s(ret, (SVDBModIfcClassDecl)it_l.get(0));
					n.setItemDecl(inst);
					ret.addChild(n);
				} else if (it instanceof ISVDBNamedItem) {
					// ERROR: Unknown module
					ret.addChild(new HierarchyTreeNode(ret, ((ISVDBNamedItem)it).getName()));
				}
			}
		}
		
		return ret;
	}

}
