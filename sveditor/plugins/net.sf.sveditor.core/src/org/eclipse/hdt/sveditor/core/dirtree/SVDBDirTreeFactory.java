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
package org.eclipse.hdt.sveditor.core.dirtree;

import org.eclipse.hdt.sveditor.core.SVFileUtils;

public class SVDBDirTreeFactory {
	
	private SVDBDirTreeNode			fRoot;
	
	public SVDBDirTreeFactory() {
		fRoot = new SVDBDirTreeNode(null, "", true);
	}
	
	public void addPath(String path, boolean is_dir) {
		path = SVFileUtils.normalize(path);
		String path_s[] = path.split("/");
		
		addPath(fRoot, path_s, 0, is_dir);
	}
	
	private void addPath(
			SVDBDirTreeNode			parent,
			String					path_s[],
			int						path_idx,
			boolean					is_dir) {
		String elem = path_s[path_idx];
		SVDBDirTreeNode child;
		
		// Check whether the child exists already
		if ((child = parent.findChild(elem)) == null) {
			// Add a new child
			child = new SVDBDirTreeNode(parent, elem,
					(is_dir || path_idx+1 != path_s.length));
			parent.addChild(child);
		}
		
		if (path_idx+1 < path_s.length) {
			addPath(child, path_s, path_idx+1, is_dir);
		}
	}
	
	/**
	 * Compact the tree and return the completed root node
	 * 
	 * @return
	 */
	public SVDBDirTreeNode buildTree() {
		// TODO: just returning the root now
		return fRoot;
	}
}
