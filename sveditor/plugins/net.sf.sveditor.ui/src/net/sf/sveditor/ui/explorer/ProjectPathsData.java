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

import org.eclipse.jface.viewers.TreeViewer;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class ProjectPathsData implements IProjectPathsData {
	private SVDBProjectData					fProjectData;
	private List<IProjectPathsData>			fPaths;
	private TreeViewer						fViewer;
	
	public ProjectPathsData(TreeViewer viewer, SVDBProjectData pd) {
		this(viewer, pd, true);
	}
	
	public ISVDBIndexIterator getIndexIt() {
		return fProjectData.getProjectIndexMgr();
	}
	
	public void reset() {
		for (IProjectPathsData p : fPaths) {
			p.reset();
		}
	}
	
	public ProjectPathsData(TreeViewer viewer, SVDBProjectData pd, boolean setup) {
		fProjectData = pd;
		fPaths = new ArrayList<IProjectPathsData>();
		fViewer = viewer;
	
		if (setup) {
			SVDBIndexCollection mgr = fProjectData.getProjectIndexMgr();

			List<ISVDBIndex> allLibIndexes = mgr.getArgFilePathList();
			List<ISVDBIndex> argFileIndexList = new ArrayList<ISVDBIndex>();

			for (ISVDBIndex i : allLibIndexes) {
				if (i.getTypeID().equals(SVDBArgFileIndexFactory.TYPE)) {
					argFileIndexList.add(i);
				}
			}

			fPaths.add(new LibIndexPath(LibIndexPath.TYPE_ARG_FILE,
					this, "Argument Files", argFileIndexList));
			fPaths.add(new PackagesExplorerData(this));
			fPaths.add(new ModulesExplorerData(this));
			fPaths.add(new ClassesExplorerData(this));
			fPaths.add(new InterfacesExplorerData(this));
		}
	}
	
	public TreeViewer getViewer() {
		return fViewer;
	}
	
	@Override
	public boolean hasChildren() {
		return (fPaths.size() > 0);
	}

	public Object[] getChildren(Object parent) {
		return fPaths.toArray();
	}

	public String getName() {
		return "SV Contents";
	}

	public Object getParent(Object element) {
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
