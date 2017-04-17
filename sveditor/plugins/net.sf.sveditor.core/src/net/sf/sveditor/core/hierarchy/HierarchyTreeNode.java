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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;

public class HierarchyTreeNode {
	
	private String							fName;
	private HierarchyTreeNode				fParent;
	private ISVDBItemBase					fItemDecl;
	private ISVDBItemBase					fItemType;
	private List<HierarchyTreeNode>			fChildren;
	
	public HierarchyTreeNode(
			HierarchyTreeNode	parent,
			String				name) {
		fName   = name;
		fParent = parent;
		fChildren = new ArrayList<HierarchyTreeNode>();
	}
	
	public HierarchyTreeNode(
			HierarchyTreeNode		parent,
			String					name,
			ISVDBItemBase			item) {
		this(parent, name);
		fItemDecl = item;
	}
	
	public HierarchyTreeNode(
			HierarchyTreeNode		parent,
			String					name,
			SVDBItem				item,
			ISVDBItemBase			type) {
		this(parent, name);
		fItemDecl = item;
		fItemType = type;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public void addChild(HierarchyTreeNode child) {
		if (!fChildren.contains(child)) {
			fChildren.add(child);
		}
	}
	
	public HierarchyTreeNode getParent() {
		return fParent;
	}
	
	public void setParent(HierarchyTreeNode parent) {
		fParent = parent;
	}
	
	public List<HierarchyTreeNode> getChildren() {
		return fChildren;
	}
	
	public ISVDBItemBase getItemDecl() {
		return fItemDecl;
	}
	
	public ISVDBItemBase getItemType() {
		return fItemType;
	}
	
	public void setItemDecl(SVDBItem cls) {
		fItemDecl = cls;
	}

}
