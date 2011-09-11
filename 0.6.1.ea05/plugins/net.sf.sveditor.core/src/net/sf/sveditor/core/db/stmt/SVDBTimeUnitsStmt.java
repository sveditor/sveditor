package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBTimeUnitsStmt extends SVDBStmt {
	private String				fUnits;
	
	public SVDBTimeUnitsStmt() {
		super(SVDBItemType.TimeUnitsStmt);
	}
	
	public String getUnits() {
		return fUnits;
	}
	
	public void setUnits(String units) {
		fUnits = units;
	}

}
