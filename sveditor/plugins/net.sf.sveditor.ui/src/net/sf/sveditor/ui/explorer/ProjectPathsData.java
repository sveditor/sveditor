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

	public Object[] getChildren(Object parent) {
		return fPaths.toArray();
	}

	public String getName() {
		return "Project Paths";
	}

	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public SVDBProjectData getProjectData() {
		return fProjectData;
	}
	
	
	
	@Override
	public int hashCode() {
		int hash = fProjectData.getName().hashCode();
		
		return hash;
	}

	public boolean equals(Object obj) {
		if (obj instanceof SVDBProjectData) {
			return (obj == fProjectData);
		} else if (obj instanceof ProjectPathsData) {
			ProjectPathsData p_obj = (ProjectPathsData)obj;
			return p_obj.getProjectData().getName().equals(
					fProjectData.getName());
		} else {
			return super.equals(obj);
		}
	}
}
