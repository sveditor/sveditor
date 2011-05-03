package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBLabeledStmt extends SVDBBodyStmt {
	private String					fLabel;
	
	public SVDBLabeledStmt() {
		super(SVDBItemType.LabeledStmt);
	}
	
	public String getLabel() {
		return fLabel;
	}
	
	public void setLabel(String label) {
		fLabel = label;
	}
	
}
