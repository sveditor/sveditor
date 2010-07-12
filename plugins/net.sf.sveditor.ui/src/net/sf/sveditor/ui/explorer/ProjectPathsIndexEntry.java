package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;

public class ProjectPathsIndexEntry implements IProjectPathsData {
	private String					fType;
	private ISVDBIndex				fIndex;
	private List<PathTreeNode>		fRoots;
	
	
	public ProjectPathsIndexEntry(String type, ISVDBIndex index) {
		fType  = type;
		fIndex = index;
		
		fRoots = new ArrayList<PathTreeNode>();

		PathTreeNodeFactory f = new PathTreeNodeFactory();
		fRoots.addAll(f.build(index.getPreProcFileMap().values()));
	}
	
	public String getType() {
		return fType;
	}

	@Override
	public Object[] getChildren(Object parent) {
		return fRoots.toArray();
	}

	@Override
	public String getName() {
		return fIndex.getBaseLocation();
	}

	@Override
	public Object getParent(Object element) {
		return null;
	}
}
