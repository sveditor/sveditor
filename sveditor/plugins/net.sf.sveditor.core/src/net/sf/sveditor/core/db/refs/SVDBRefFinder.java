package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBLocation;

public class SVDBRefFinder extends AbstractSVDBFileRefFinder {
	private SVDBRefType				fRefType;
	private String					fRefName;
	private List<SVDBRefItem>		fRefList;
	
	public SVDBRefFinder(
			SVDBRefType		ref_type,
			String			ref_name) {
		fRefList = new ArrayList<SVDBRefItem>();
		fRefType = ref_type;
		fRefName = ref_name;
	}
	
	public List<SVDBRefItem> find_refs(SVDBFile file) {
		visitFile(file);
		return fRefList;
	}

	@Override
	protected void visitRef(SVDBLocation loc, SVDBRefType type, String name) {
		if (type == fRefType && name.equals(fRefName)) {
			List<ISVDBItemBase> ref_path = new ArrayList<ISVDBItemBase>();
			ref_path.addAll(fScopeStack);
			fRefList.add(new SVDBRefItem(ref_path, fRefName, fRefType));
		}
	}
}
