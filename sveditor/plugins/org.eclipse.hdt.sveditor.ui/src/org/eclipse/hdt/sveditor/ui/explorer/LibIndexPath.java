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


package org.eclipse.hdt.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;

public class LibIndexPath implements IProjectPathsData {
	public static final String			TYPE_LIB_PATH       = "LIB_PATH";
	public static final String			TYPE_SRC_COLLECTION = "SRC_COLLECTION";
	public static final String			TYPE_ARG_FILE       = "ARG_FILE";
	
	private IProjectPathsData				fParent;
	private String							fName;
	private String							fType;
	private List<ProjectPathsIndexEntry>	fIndexList;
	
	public LibIndexPath(
			String				type,
			IProjectPathsData 	parent,
			String 				name,
			List<ISVDBIndex>	index_list) {
		fType   = type;
		fParent = parent;
		fName   = name;
		fIndexList = new ArrayList<ProjectPathsIndexEntry>();
		
		for (ISVDBIndex index : index_list) {
			ProjectPathsIndexEntry e = new ProjectPathsIndexEntry(type, index);
			fIndexList.add(e);
		}
	}
	
	public String getType() {
		return fType;
	}
	
	public void reset() { }
	
	@Override
	public boolean hasChildren() {
		return (fIndexList.size() > 0);
	}

	public Object[] getChildren(Object parent) {
		return fIndexList.toArray();
	}

	public String getName() {
		return fName;
	}

	public Object getParent(Object element) {
		if (element == this) {
			return fParent;
		}
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public int hashCode() {
		int hash = fName.hashCode();
		hash += fType.hashCode();
		hash += fParent.hashCode();
		
		return hash;
	}

	public boolean equals(Object obj) {
		if (obj instanceof LibIndexPath) {
			LibIndexPath lip = (LibIndexPath)obj;
			return (fName.equals(lip.fName) &&
					fType.equals(lip.fType) &&
					fParent.equals(lip.fParent));
		} else {
			return super.equals(obj);
		}
	}
}
