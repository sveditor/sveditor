/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;

public class PathTreeNode implements IProjectPathsData {
	private String					fName;
	private List<SVDBFile>			fFileList;
	private List<PathTreeNode>		fChildNodes;
	
	public PathTreeNode(String name) {
		fName = name;
		fFileList = new ArrayList<SVDBFile>();
		fChildNodes = new ArrayList<PathTreeNode>();
	}
	
	public List<SVDBFile> getFileList() {
		return fFileList;
	}
	
	public List<PathTreeNode> getChildNodes() {
		return fChildNodes;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}

	public Object[] getChildren(Object parent) {
		List<Object> ret = new ArrayList<Object>();
		ret.addAll(fChildNodes);
		ret.addAll(fFileList);
		
		return ret.toArray();
	}

	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

}
