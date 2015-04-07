package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVDBRandseqProdStmt extends SVDBStmt {
	public SVDBTypeInfo			fRetType;
	public String				fName;
	
	public SVDBRandseqProdStmt() {
		super(SVDBItemType.RandseqProdStmt);
	}
	
	public void setRetType(SVDBTypeInfo type) {
		fRetType = type;
	}
	
	public SVDBTypeInfo getRetType() {
		return fRetType;
	}

	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
}
