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
package net.sf.sveditor.core.dirtree;

import java.util.ArrayList;
import java.util.List;

public class SVDBDirTreeNode {
	private String					fName;
	private boolean				fIsDir;
	private SVDBDirTreeNode			fParent;
	private List<SVDBDirTreeNode>	fChildren;
	
	public SVDBDirTreeNode(
			SVDBDirTreeNode			parent,
			String					name,
			boolean					is_dir) {
		fParent = parent;
		fName = name;
		fIsDir = is_dir;
		fChildren = new ArrayList<SVDBDirTreeNode>();
	}
	
	public void addChild(SVDBDirTreeNode node) {
		fChildren.add(node);
	}
	
	public List<SVDBDirTreeNode> getChildren() {
		return fChildren;
	}
	
	public boolean isDir() {
		return fIsDir;
	}
	
	public String getName() {
		return fName;
	}

	public SVDBDirTreeNode getParent() {
		return fParent;
	}
	
	public SVDBDirTreeNode findChild(String name) {
		for (SVDBDirTreeNode n : fChildren) {
			if (n.getName().equals(name)) {
				return n;
			}
		}
		return null;
	}

	@Override
	public int hashCode() {
		return fName.hashCode();
	}
	
}
