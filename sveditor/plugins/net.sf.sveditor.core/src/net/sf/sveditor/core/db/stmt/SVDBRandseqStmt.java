package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRandseqStmt extends SVDBStmt {
	
	public String				fName;
	
	public SVDBRandseqStmt() {
		super(SVDBItemType.RandseqStmt);
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}

}
