package net.sf.sveditor.core.db.refs;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;

public class SVDBRefItem {
	private List<ISVDBItemBase>			fRefPath;
	private String						fRefName;
	private SVDBRefType					fRefType;
	
	public SVDBRefItem(
			List<ISVDBItemBase>			ref_path,
			String						ref_name,
			SVDBRefType					ref_type) {
		fRefPath = ref_path;
		fRefName = ref_name;
		fRefType = ref_type;
	}

	public SVDBFile getRoot() {
		return (SVDBFile)fRefPath.get(0);
	}
	
	public ISVDBItemBase getLeaf() {
		return fRefPath.get(fRefPath.size()-1);
	}

}
