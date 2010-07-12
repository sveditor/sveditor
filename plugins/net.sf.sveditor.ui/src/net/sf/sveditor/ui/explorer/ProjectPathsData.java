package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class ProjectPathsData implements IProjectPathsData {
	private SVDBProjectData					fProjectData;
	private List<IProjectPathsData>			fPaths;
	
	public ProjectPathsData(SVDBProjectData pd) {
		fProjectData = pd;
		fPaths = new ArrayList<IProjectPathsData>();
		
		SVDBIndexCollectionMgr mgr = fProjectData.getProjectIndexMgr();
		
		List<ISVDBIndex> allLibIndexes = mgr.getLibraryPathList();
		List<ISVDBIndex> srcCollectionIndexes = mgr.getSourceCollectionList();
		List<ISVDBIndex> libIndexList = new ArrayList<ISVDBIndex>();
		List<ISVDBIndex> argFileIndexList = new ArrayList<ISVDBIndex>();
		
		for (ISVDBIndex i : allLibIndexes) {
			if (i.getTypeID().equals(SVDBArgFileIndexFactory.TYPE)) {
				argFileIndexList.add(i);
			} else {
				libIndexList.add(i);
			}
		}
		
		fPaths.add(new LibIndexPath(LibIndexPath.TYPE_SRC_COLLECTION,
				this, "Source Collections", srcCollectionIndexes));
		fPaths.add(new LibIndexPath(LibIndexPath.TYPE_LIB_PATH,
				this, "Library Paths", libIndexList));
		fPaths.add(new LibIndexPath(LibIndexPath.TYPE_ARG_FILE,
				this, "Argument Files", argFileIndexList));
	}

	@Override
	public Object[] getChildren(Object parent) {
		return fPaths.toArray();
	}

	@Override
	public String getName() {
		return "Project Paths";
	}

	@Override
	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}
	

	

}
