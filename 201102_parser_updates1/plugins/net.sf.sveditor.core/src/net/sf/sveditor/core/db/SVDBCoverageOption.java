package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBCoverageOption extends SVDBStmt {
	private boolean			fIsTypeOption;
	private String			fName;
	private SVExpr			fExpr;
	
	public SVDBCoverageOption(String name, boolean is_type_option) {
		super(SVDBItemType.CoverageOptionStmt);
		fName = name;
		fIsTypeOption = is_type_option;
	}
	
	public boolean isTypeOption() {
		return fIsTypeOption;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	

}
