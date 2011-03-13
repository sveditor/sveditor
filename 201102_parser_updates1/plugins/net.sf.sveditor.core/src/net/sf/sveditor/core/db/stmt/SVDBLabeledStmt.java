package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBLabeledStmt extends SVDBStmt {
	private String					fLabel;
	private SVDBStmt				fStmt;
	
	public SVDBLabeledStmt() {
		super(SVDBItemType.LabeledStmt);
	}
	
	public SVDBLabeledStmt(String label, SVDBStmt stmt) {
		super(SVDBItemType.LabeledStmt);
		fLabel = label;
	}
	
	public String getLabel() {
		return fLabel;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}

}
