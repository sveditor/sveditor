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
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;


public class ObjectsTreeFactory {
	List<ISVDBIndex> fProjectIndexList ;
	
	public ObjectsTreeFactory(List<ISVDBIndex> projectIndexList) {
		fProjectIndexList = projectIndexList;
	}
	
	public ObjectsTreeNode build() { 
		
		if(fProjectIndexList == null) {
			return null ;
		}
		
		ObjectsTreeNode topNode  = new ObjectsTreeNode(null, "Top") ;
		
		// TODO: spin through the incoming projectIndexList and produce the real tree.
		// 		 Currently generating some phony data
		
		ObjectsTreeNode packagesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.PACKAGES_NODE) ;
		topNode.addChild(packagesNode) ;
		packagesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.PACKAGES_NODE, SVDBItemType.PackageDecl)) ;
		
		for(String pkgName: Arrays.asList("axi_agent_pkg", "cpu_agent_pkg")) {
			SVDBDeclCacheItem pkgDeclItem = new SVDBDeclCacheItem(null, null, pkgName, SVDBItemType.PackageDecl) ;
			ObjectsTreeNode pkgNode = new ObjectsTreeNode(packagesNode, pkgName, pkgDeclItem) ;  
			packagesNode.addChild(pkgNode) ; 
			for(String className: Arrays.asList("bfm", "mon", "agent")) {
				SVDBDeclCacheItem classDeclItem = new SVDBDeclCacheItem(null, null, className, SVDBItemType.ClassDecl) ;
				ObjectsTreeNode classNode = new ObjectsTreeNode(pkgNode, className, classDeclItem); 
				pkgNode.addChild(classNode) ; 
			}
		}
		
		ObjectsTreeNode modulesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.MODULES_NODE) ;
		topNode.addChild(modulesNode) ;
		modulesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.MODULES_NODE, SVDBItemType.ModuleDecl)) ;
		
		for(String pkgName: Arrays.asList("axi", "cpu")) {
			SVDBDeclCacheItem moduleDeclItem = new SVDBDeclCacheItem(null, null, pkgName, SVDBItemType.ModuleDecl) ;
			ObjectsTreeNode moduleNode = new ObjectsTreeNode(packagesNode, pkgName, moduleDeclItem) ;  
			modulesNode.addChild(moduleNode) ; 
		}
		
		ObjectsTreeNode interfacesNode = new ObjectsTreeNode(topNode, ObjectsTreeNode.INTERFACES_NODE) ;
		topNode.addChild(interfacesNode) ;
		interfacesNode.setItemDecl(new SVDBDeclCacheItem(null, null, ObjectsTreeNode.INTERFACES_NODE, SVDBItemType.InterfaceDecl)) ;
		
		for(String pkgName: Arrays.asList("axi", "cpu")) {
			SVDBDeclCacheItem interfaceDeclItem = new SVDBDeclCacheItem(null, null, pkgName, SVDBItemType.InterfaceDecl) ;
			ObjectsTreeNode moduleNode = new ObjectsTreeNode(packagesNode, pkgName, interfaceDeclItem) ;  
			interfacesNode.addChild(moduleNode) ; 
		}
		
		return topNode ;
		
	}
		
}
