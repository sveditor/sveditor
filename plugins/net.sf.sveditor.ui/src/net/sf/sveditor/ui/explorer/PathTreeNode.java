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

	@Override
	public Object[] getChildren(Object parent) {
		List<Object> ret = new ArrayList<Object>();
		ret.addAll(fChildNodes);
		ret.addAll(fFileList);
		
		return ret.toArray();
	}

	@Override
	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

}
