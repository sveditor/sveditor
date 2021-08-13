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
package org.sveditor.core.design_hierarchy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.SVProjectNature;
import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBModIfcDecl;
import org.sveditor.core.db.SVDBModIfcInst;
import org.sveditor.core.db.SVDBModIfcInstItem;
import org.sveditor.core.db.SVDBModuleDecl;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.index.SVDBIndexCollection;
import org.sveditor.core.db.project.SVDBProjectData;
import org.sveditor.core.db.project.SVDBProjectManager;
import org.sveditor.core.db.refs.SVDBFindReferencesOp;
import org.sveditor.core.db.refs.SVDBRefMayContainVisitor;
import org.sveditor.core.db.refs.SVDBRefSearchSpecModIfcRefsByName;
import org.sveditor.core.db.refs.ISVDBRefSearchSpec.NameMatchType;
import org.sveditor.core.db.search.SVDBFindByNameMatcher;
import org.sveditor.core.db.search.SVDBFindByTypeMatcher;

public class DesignHierarchyContentProviderBase {
	
	protected Map<IProject, List<SVDBModuleDecl>>	fRootMap;
	protected SVDBFindByNameMatcher					fNameMatcher = new SVDBFindByNameMatcher();
	
	public DesignHierarchyContentProviderBase() {
		fRootMap = new HashMap<IProject, List<SVDBModuleDecl>>();
	}
	
	public void build(IProgressMonitor monitor) {
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		fRootMap.clear();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

		IProject projects[] = root.getProjects();
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Build Design Hierarchy", 1000*projects.length);
		
		for (IProject p : projects) {
			if (SVProjectNature.hasSvProjectNature(p)) {
				SVDBProjectData pdata = pmgr.getProjectData(p);
				SVDBIndexCollection index = pdata.getProjectIndexMgr();
				
				List<SVDBDeclCacheItem> module_l = index.findGlobalScopeDecl(
						new NullProgressMonitor(), "", 
						new SVDBFindByTypeMatcher(SVDBItemType.ModuleDecl));
				SubMonitor loopMonitor = subMonitor.newChild(1000);
				loopMonitor.beginTask("Checking module declarations", 100*module_l.size());
//				System.out.println("module_l.size=" + module_l.size());
				
				List<SVDBModuleDecl> root_list = new ArrayList<SVDBModuleDecl>();
				
				for (SVDBDeclCacheItem module_it : module_l) {
//					SVDBModuleDecl module = (SVDBModuleDecl)module_it.getSVDBItem();
					SVDBRefMayContainVisitor visitor = new SVDBRefMayContainVisitor();

					pdata.getProjectIndexMgr().execOp(
							new NullProgressMonitor(),
							new SVDBFindReferencesOp(new SVDBRefSearchSpecModIfcRefsByName(
											module_it.getName(), 
											NameMatchType.MayContain), visitor),
									false);
					
					if (!visitor.mayContain()) {
						if (module_it.getSVDBItem() != null) {
							root_list.add((SVDBModuleDecl)module_it.getSVDBItem());
						}
					}
					loopMonitor.worked(100);
				}
				
				loopMonitor.done();
				
				fRootMap.put(p, root_list);
			} else {
				subMonitor.worked(1000);
			}
		}
		
		subMonitor.done();
	}
	
	public Set<IProject> getRoots() {
		return fRootMap.keySet();
	}
	
	
	public Object[] getChildren(Object parent) {
		if (parent instanceof IProject) {
			List<DesignHierarchyNode> ret = new ArrayList<DesignHierarchyNode>();
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			ISVDBIndexIterator index_it = pmgr.getProjectData((IProject)parent).getProjectIndexMgr();
			
			for (SVDBModuleDecl d : fRootMap.get(parent)) {
				ret.add(new DesignHierarchyNode(index_it, d, parent));
			}
			return ret.toArray();
		} else if (parent instanceof DesignHierarchyNode) {
			DesignHierarchyNode dn = (DesignHierarchyNode)parent;
			List<DesignHierarchyNode> ret = new ArrayList<DesignHierarchyNode>();
			Object target = dn.getTarget();
			SVDBModIfcDecl module_decl = null;
			
			if (target instanceof SVDBModuleDecl) {
				module_decl = (SVDBModuleDecl)target;
			} else if (target instanceof SVDBModIfcInstItem) {
				SVDBModIfcInstItem inst_it = (SVDBModIfcInstItem)target;
				SVDBModIfcInst mod_inst = (SVDBModIfcInst)inst_it.getParent();
				
				String typename = mod_inst.getTypeName();
				List<SVDBDeclCacheItem> item = dn.getIndexIt().findGlobalScopeDecl(
						new NullProgressMonitor(), typename, fNameMatcher);
				if (item.size() > 0) {
					module_decl = (SVDBModIfcDecl)item.get(0).getSVDBItem();
//					ret.add(new DesignHierarchyNode(dn.getIndexIt(),
//							item.get(0).getSVDBItem(), dn));
				}
			}
			
			// Compute children
			if (module_decl != null) {
				for (ISVDBChildItem ci : module_decl.getChildren()) {
					if (ci.getType() == SVDBItemType.ModIfcInst) {
						for (ISVDBChildItem mod_inst_it : ((SVDBModIfcInst)ci).getChildren()) {
							ret.add(new DesignHierarchyNode(dn.getIndexIt(), mod_inst_it, dn));
						}
					}
				}
			}
			
			return ret.toArray();
		} else {
			return new Object[0];
		}
	}
	
	public boolean hasChildren(Object parent) {
		if (parent instanceof IProject) {
			if (fRootMap.containsKey(parent)) {
				return true;
			}
		} else if (parent instanceof DesignHierarchyNode) {
			DesignHierarchyNode dn = (DesignHierarchyNode)parent;
			
			if (dn.getTarget() instanceof SVDBModIfcDecl) {
				for (ISVDBChildItem ci : ((SVDBModIfcDecl)dn.getTarget()).getChildren()) {
					if (ci.getType() == SVDBItemType.ModIfcInst) {
						return true;
					}
				}
			} else {
				return (getChildren(parent).length > 0);
			}
		} 
		
		return false;
	}
}
