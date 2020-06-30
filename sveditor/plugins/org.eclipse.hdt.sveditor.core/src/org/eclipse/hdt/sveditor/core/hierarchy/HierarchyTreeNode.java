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
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.hierarchy;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;

public class HierarchyTreeNode {
	
	private String							fName;
	private HierarchyTreeNode				fParent;
	private ISVDBItemBase					fItemDecl;
	private SVDBDeclCacheItem				fAltItemDecl;
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
			ISVDBItemBase			item,
			SVDBDeclCacheItem		alt_item) {
		this(parent, name, item);
		fAltItemDecl = alt_item;
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
	
	public SVDBDeclCacheItem getAltItemDecl() {
		return fAltItemDecl;
	}
	
	public ISVDBItemBase getItemType() {
		return fItemType;
	}
	
	public void setItemDecl(SVDBItem cls) {
		fItemDecl = cls;
	}

}
