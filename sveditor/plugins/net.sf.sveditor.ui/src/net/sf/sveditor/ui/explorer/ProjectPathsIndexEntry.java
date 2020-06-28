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


package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.dirtree.SVDBDirTreeFactory;
import net.sf.sveditor.core.dirtree.SVDBDirTreeNode;

import org.eclipse.core.runtime.NullProgressMonitor;

public class ProjectPathsIndexEntry implements IProjectPathsData {
	private String					fType;
	private ISVDBIndex				fIndex;
	private List<SVDBDirTreeNode>	fRoots;
	
	
	public ProjectPathsIndexEntry(String type, ISVDBIndex index) {
		fType  = type;
		fIndex = index;
		
		fRoots = new ArrayList<SVDBDirTreeNode>();
		
		Iterable<String> filelist = fIndex.getFileList(new NullProgressMonitor());
		
		SVDBDirTreeFactory tree_factory = new SVDBDirTreeFactory();
		for (String f : filelist) {
			tree_factory.addPath(f, false); // TODO: determine item type
		}
		fRoots.addAll(tree_factory.buildTree().getChildren());

		// TODO: remove elements up to the start of the root (?)
	}
	
	public void reset() { }
	
	public String getType() {
		return fType;
	}

	
	@Override
	public boolean hasChildren() {
		return (fRoots.size() > 0);
	}

	public Object[] getChildren(Object parent) {
		return fRoots.toArray();
	}

	public String getName() {
		return fIndex.getBaseLocation();
	}

	public Object getParent(Object element) {
		return null;
	}
}
