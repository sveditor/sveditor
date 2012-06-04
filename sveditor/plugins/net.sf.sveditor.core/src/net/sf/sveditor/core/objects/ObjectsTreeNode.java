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

import java.util.ArrayList;
import java.util.List;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class ObjectsTreeNode {
	
	private String					fName; // FIXME: DeclCacheItem has a name. This seems redundant
	private ObjectsTreeNode			fParent;
	private SVDBDeclCacheItem		fItemDecl;
	private List<ObjectsTreeNode>	fChildren;
	
	public static String MODULES_NODE = "Modules" ;
	public static String INTERFACES_NODE = "Interfaces" ;
	public static String PACKAGES_NODE = "Packages" ;
	
	public ObjectsTreeNode(
			ObjectsTreeNode	parent,
			String				name) {
		fName   = name;
		fParent = parent;
		fChildren = new ArrayList<ObjectsTreeNode>();
	}
	
	public ObjectsTreeNode(
			ObjectsTreeNode		parent,
			String					name,
			SVDBDeclCacheItem				item) {
		this(parent, name);
		fItemDecl = item;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public void addChild(ObjectsTreeNode child) {
		if (!fChildren.contains(child)) {
			fChildren.add(child);
		}
	}
	
	public ObjectsTreeNode getChildByName(String name) {
		for(ObjectsTreeNode child: getChildren()) {
			if(child.getName() == name) {
				return child ;
			}
		}
		return null ;
	}
	
	public ObjectsTreeNode getParent() {
		return fParent;
	}
	
	public void setParent(ObjectsTreeNode parent) {
		fParent = parent;
	}
	
	public List<ObjectsTreeNode> getChildren() {
		return fChildren;
	}
	
	public SVDBDeclCacheItem getItemDecl() {
		return fItemDecl;
	}
	
	public void setItemDecl(SVDBDeclCacheItem cls) {
		fItemDecl = cls;
	}

}
