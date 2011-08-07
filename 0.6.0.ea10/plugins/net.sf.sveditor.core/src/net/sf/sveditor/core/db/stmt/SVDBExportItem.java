package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBExportItem extends SVDBStmt {
	
	private String				fExport;
	
	public SVDBExportItem() {
		super(SVDBItemType.ExportItem);
	}
	
	public String getExport() {
		return fExport;
	}
	
	public void setExport(String exp) {
		fExport = exp;
	}

}
