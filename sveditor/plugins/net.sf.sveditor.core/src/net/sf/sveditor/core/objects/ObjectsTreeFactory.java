/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 *     Armond Paiva - repurposed from hierarchy to objects view
 ****************************************************************************/


package net.sf.sveditor.core.objects;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindClassMatcher;
import net.sf.sveditor.core.db.search.SVDBFindInterfaceMatcher;
import net.sf.sveditor.core.db.search.SVDBFindModuleMatcher;
import net.sf.sveditor.core.db.search.SVDBFindPackageMatcher;


public class ObjectsTreeFactory {
	List<ISVDBIndex> fProjectIndexList ;
	
	public ObjectsTreeFactory(List<ISVDBIndex> projectIndexList) {
		fProjectIndexList = projectIndexList;
	}
	
	public ObjectsTreeNode build() { 
		
		if(fProjectIndexList == null) {
			return null ;
		}
		
		Map<String,SVDBDeclCacheItem> pkgMap = new HashMap<String, SVDBDeclCacheItem>();
		Map<String,SVDBDeclCacheItem> globalPkgMap = new HashMap<String, SVDBDeclCacheItem>() ;
		Map<String,SVDBDeclCacheItem> ifaceMap = new HashMap<String, SVDBDeclCacheItem>() ;
		Map<String,SVDBDeclCacheItem> moduleMap = new HashMap<String, SVDBDeclCacheItem>() ;
		
		ObjectsTreeNode topNode  = new ObjectsTreeNode(null, "Top") ;
		
		// TODO: spin through the incoming projectIndexList and produce the real tree.
		// 		 Currently generating some phony data
		
		ObjectsTreeNode packagesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.PACKAGES_NODE) ;
		topNode.addChild(packagesNode) ;
		packagesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.PACKAGES_NODE, SVDBItemType.PackageDecl)) ;
		
		ObjectsTreeNode rootPkgNode = new ObjectsTreeNode(packagesNode, "root") ;
		packagesNode.addChild(rootPkgNode) ;
		rootPkgNode.setItemDecl(new SVDBDeclCacheItem(null, null, "root", SVDBItemType.PackageDecl)) ;
		
		// Global classes go into the "root" package
		//
		for(ISVDBIndex svdbIndex: fProjectIndexList) {
			List<SVDBDeclCacheItem> rootClasses = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(), "rootClasses", new SVDBFindClassMatcher()) ;
			if(rootClasses != null) {
				for(SVDBDeclCacheItem rootClass: rootClasses) {
					if(rootClass.getName().matches("^__.*")) { continue ; } // Skip builtins
					if(!globalPkgMap.containsKey(rootClass.getName())) {
						ObjectsTreeNode rootClassNode = new ObjectsTreeNode(rootPkgNode, rootClass.getName(), rootClass) ;  
						rootPkgNode.addChild(rootClassNode) ; 
						globalPkgMap.put(rootClass.getName(), rootClass) ;
					}
				}
			}
		}
		
		for(ISVDBIndex svdbIndex: fProjectIndexList) {
			List<SVDBDeclCacheItem> packages = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(), "pkgs", new SVDBFindPackageMatcher()) ;
			if(packages != null) {
				for(SVDBDeclCacheItem pkg: packages) {
					if(!pkgMap.containsKey(pkg.getName())) {
						ObjectsTreeNode pkgNode = new ObjectsTreeNode(packagesNode, pkg.getName(), pkg) ;  
						packagesNode.addChild(pkgNode) ; 
						pkgMap.put(pkg.getName(), pkg) ;
					}
				}
			}
		}
		
//		for(String pkgName: Arrays.asList("axi_agent_pkg", "cpu_agent_pkg")) {
//			SVDBDeclCacheItem pkgDeclItem = new SVDBDeclCacheItem(null, null, pkgName, SVDBItemType.PackageDecl) ;
//			ObjectsTreeNode pkgNode = new ObjectsTreeNode(packagesNode, pkgName, pkgDeclItem) ;  
//			packagesNode.addChild(pkgNode) ; 
//			for(String className: Arrays.asList("bfm", "mon", "agent")) {
//				SVDBDeclCacheItem classDeclItem = new SVDBDeclCacheItem(null, null, className, SVDBItemType.ClassDecl) ;
//				ObjectsTreeNode classNode = new ObjectsTreeNode(pkgNode, className, classDeclItem); 
//				pkgNode.addChild(classNode) ; 
//			}
//		}
		
		ObjectsTreeNode modulesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.MODULES_NODE) ;
		topNode.addChild(modulesNode) ;
		modulesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.MODULES_NODE, SVDBItemType.ModuleDecl)) ;
		
		for(ISVDBIndex svdbIndex: fProjectIndexList) {
			List<SVDBDeclCacheItem> modules = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(), "modules", new SVDBFindModuleMatcher()) ;
			if(modules != null) {
				for(SVDBDeclCacheItem module: modules) {
					if(!moduleMap.containsKey(module.getName())) {
						ObjectsTreeNode moduleNode = new ObjectsTreeNode(modulesNode, module.getName(), module) ;  
						modulesNode.addChild(moduleNode) ; 
						moduleMap.put(module.getName(),module) ;
					}
				}
			}
		}
		
		
//		for(String pkgName: Arrays.asList("axi", "cpu")) {
//			SVDBDeclCacheItem moduleDeclItem = new SVDBDeclCacheItem(null, null, pkgName, SVDBItemType.ModuleDecl) ;
//			ObjectsTreeNode moduleNode = new ObjectsTreeNode(packagesNode, pkgName, moduleDeclItem) ;  
//			modulesNode.addChild(moduleNode) ; 
//		}
		
		ObjectsTreeNode interfacesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.INTERFACES_NODE) ;
		topNode.addChild(interfacesNode) ;
		interfacesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.INTERFACES_NODE, SVDBItemType.InterfaceDecl)) ;
		
		for(ISVDBIndex svdbIndex: fProjectIndexList) {
			List<SVDBDeclCacheItem> interfaces = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(), "interfaces", new SVDBFindInterfaceMatcher()) ;
			if(interfaces != null) {
				for(SVDBDeclCacheItem iface: interfaces) {
					if(!ifaceMap.containsKey(iface.getName())) {
						ObjectsTreeNode ifaceNode = new ObjectsTreeNode(interfacesNode, iface.getName(), iface) ;  
						interfacesNode.addChild(ifaceNode) ; 
						ifaceMap.put(iface.getName(),iface) ;
					}
				}
			}
		}
		
		
//		for(String pkgName: Arrays.asList("axi", "cpu")) {
//			SVDBDeclCacheItem interfaceDeclItem = new SVDBDeclCacheItem(null, null, pkgName, SVDBItemType.InterfaceDecl) ;
//			ObjectsTreeNode moduleNode = new ObjectsTreeNode(packagesNode, pkgName, interfaceDeclItem) ;  
//			interfacesNode.addChild(moduleNode) ; 
//		}
		
		return topNode ;
		
	}
		
}
