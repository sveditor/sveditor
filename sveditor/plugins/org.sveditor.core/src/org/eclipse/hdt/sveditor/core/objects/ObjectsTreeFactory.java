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
 *     Armond Paiva - repurposed from hierarchy to objects view
 ****************************************************************************/


package org.sveditor.core.objects;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.search.SVDBFindClassMatcher;
import org.sveditor.core.db.search.SVDBFindInterfaceMatcher;
import org.sveditor.core.db.search.SVDBFindModuleMatcher;
import org.sveditor.core.db.search.SVDBFindPackageMatcher;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;


public class ObjectsTreeFactory {
	List<ISVDBIndex> fProjectIndexList ;
	private LogHandle				fLog;
	
	public ObjectsTreeFactory(List<ISVDBIndex> projectIndexList) {
		fProjectIndexList = projectIndexList;
		fLog = LogFactory.getLogHandle("ObjectsTreeFactory");
	}
	
	public ObjectsTreeNode build() { 
		
		if(fProjectIndexList == null) {
			return null ;
		}
		
		Map<String,SVDBDeclCacheItem> pkgMap = new HashMap<String, SVDBDeclCacheItem>();
		Map<String,SVDBDeclCacheItem> globalPkgMap = new HashMap<String, SVDBDeclCacheItem>() ;
		Map<String,SVDBDeclCacheItem> ifaceMap = new HashMap<String, SVDBDeclCacheItem>() ;
		Map<String,SVDBDeclCacheItem> moduleMap = new HashMap<String, SVDBDeclCacheItem>() ;
		Map<String,SVDBDeclCacheItem> classMap = new HashMap<String, SVDBDeclCacheItem>() ;
		
		ObjectsTreeNode topNode  = new ObjectsTreeNode(null, "Top") ;
		
		ObjectsTreeNode packagesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.PACKAGES_NODE) ;
		topNode.addChild(packagesNode) ;
		packagesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.PACKAGES_NODE, SVDBItemType.PackageDecl, false)) ;
		
		ObjectsTreeNode rootPkgNode = new ObjectsTreeNode(packagesNode, "root") ;
		packagesNode.addChild(rootPkgNode) ;
		rootPkgNode.setItemDecl(new SVDBDeclCacheItem(null, null, "root", SVDBItemType.PackageDecl, false)) ;
		
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
						// Look deeper into this project to find all classes for this package
						List<SVDBDeclCacheItem> pkgDecls = svdbIndex.findPackageDecl(new NullProgressMonitor(), pkg) ; 
						if(pkgDecls != null) {
							fLog.debug("Package Declaration for \"" + pkg.getName() + "\" found");
							for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
								if(pkgDecl.getType() == SVDBItemType.ClassDecl) {
									fLog.debug("  Add node for \"" + pkgDecl.getName() + "\"");
									ObjectsTreeNode pkgClassNode = new ObjectsTreeNode(pkgNode, pkgDecl.getName(), pkgDecl) ;
									pkgNode.addChild(pkgClassNode) ;
								}
							}
						} else {
							fLog.debug("Package Declaration for \"" + pkg.getName() + "\" not found");
						}
					}
				}
			}
		}
		
		ObjectsTreeNode modulesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.MODULES_NODE) ;
		topNode.addChild(modulesNode) ;
		modulesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.MODULES_NODE, SVDBItemType.ModuleDecl, false)) ;
		
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
		
		ObjectsTreeNode classesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.CLASSES_NODE) ;
		topNode.addChild(classesNode) ;
		classesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.CLASSES_NODE, SVDBItemType.ClassDecl, false)) ;
		
		for(ISVDBIndex svdbIndex: fProjectIndexList) {
			List<SVDBDeclCacheItem> classes = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(), null, new SVDBFindClassMatcher()) ;
			if(classes != null) {
				for(SVDBDeclCacheItem cls: classes) {
					if(!classMap.containsKey(cls.getName())) {
						ObjectsTreeNode classNode = new ObjectsTreeNode(modulesNode, cls.getName(), cls) ;  
						classesNode.addChild(classNode) ; 
						classMap.put(cls.getName(),cls) ;
					}
				}
			}
		}	
		
		ObjectsTreeNode interfacesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.INTERFACES_NODE) ;
		topNode.addChild(interfacesNode) ;
		interfacesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.INTERFACES_NODE, SVDBItemType.InterfaceDecl, false)) ;
		
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
		
		return topNode ;
		
	}
		
}
