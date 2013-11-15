package net.sf.sveditor.core.design_hierarchy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.refs.SVDBFindReferencesOp;
import net.sf.sveditor.core.db.refs.SVDBRefCollectorVisitor;
import net.sf.sveditor.core.db.refs.SVDBRefSearchByNameSpec;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

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
		monitor.beginTask("Build Design Hierarchy", 1000*projects.length);
		
		for (IProject p : projects) {
			if (SVProjectNature.hasSvProjectNature(p)) {
				SVDBProjectData pdata = pmgr.getProjectData(p);
				SVDBIndexCollection index = pdata.getProjectIndexMgr();
				
				List<SVDBDeclCacheItem> module_l = index.findGlobalScopeDecl(
						new NullProgressMonitor(), "", 
						new SVDBFindByTypeMatcher(SVDBItemType.ModuleDecl));
				
				List<SVDBModuleDecl> root_list = new ArrayList<SVDBModuleDecl>();
				
				for (SVDBDeclCacheItem module_it : module_l) {
					SVDBModuleDecl module = (SVDBModuleDecl)module_it.getSVDBItem();
					SVDBRefCollectorVisitor visitor = new SVDBRefCollectorVisitor();

					if (module != null) {
						pdata.getProjectIndexMgr().execOp(monitor, 
								new SVDBFindReferencesOp(
									new SVDBRefSearchByNameSpec(module.getName()),
									visitor), 
									false);
						if (visitor.getItemList().size() == 0) {
							root_list.add(module);
						}
					}
				}
				
				fRootMap.put(p, root_list);
			}
		}
		
		monitor.done();
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
			SVDBModuleDecl module_decl = null;
			
			if (target instanceof SVDBModuleDecl) {
				module_decl = (SVDBModuleDecl)target;
			} else if (target instanceof SVDBModIfcInstItem) {
				SVDBModIfcInstItem inst_it = (SVDBModIfcInstItem)target;
				SVDBModIfcInst mod_inst = (SVDBModIfcInst)inst_it.getParent();
				
				String typename = mod_inst.getTypeName();
				List<SVDBDeclCacheItem> item = dn.getIndexIt().findGlobalScopeDecl(
						new NullProgressMonitor(), typename, fNameMatcher);
				if (item.size() > 0) {
					module_decl = (SVDBModuleDecl)item.get(0).getSVDBItem();
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
}
