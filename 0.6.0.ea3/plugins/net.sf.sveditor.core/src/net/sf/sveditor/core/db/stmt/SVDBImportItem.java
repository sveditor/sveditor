package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBImportItem extends SVDBStmt {
	private String			fImport;
	
	public SVDBImportItem() {
		super(SVDBItemType.ImportItem);
	}
	
	public String getImport() {
		return fImport;
	}
	
	public void setImport(String imp) {
		fImport = imp;
	}

}
