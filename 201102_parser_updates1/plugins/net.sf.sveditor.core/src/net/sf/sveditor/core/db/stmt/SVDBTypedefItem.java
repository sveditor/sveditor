package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBTypedefItem extends SVDBStmt implements ISVDBNamedItem {
	private String				fName;
	
	public SVDBTypedefItem() {
		super(SVDBItemType.TypedefItem);
	}
	
	public SVDBTypedefItem(String name) {
		super(SVDBItemType.TypedefItem);
	}
	
	public void setName(String name) {
		fName = name;
	}

	public String getName() {
		return fName;
	}

	
}
