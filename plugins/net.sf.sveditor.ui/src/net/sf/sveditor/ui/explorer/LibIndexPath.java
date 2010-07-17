package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;

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
}
