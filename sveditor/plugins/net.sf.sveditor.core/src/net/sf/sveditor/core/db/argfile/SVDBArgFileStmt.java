package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.attr.SVDBParentAttr;

public class SVDBArgFileStmt extends SVDBItemBase implements ISVDBChildItem {
	@SVDBParentAttr
	public ISVDBChildItem			fParent;
	
	public SVDBArgFileStmt(SVDBItemType type) {
		super(type);
	}

	public ISVDBChildItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

}
