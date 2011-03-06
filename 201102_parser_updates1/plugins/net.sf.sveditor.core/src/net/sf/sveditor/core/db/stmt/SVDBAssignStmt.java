package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBAssignStmt extends SVDBStmt {
	private SVExpr			fLHS;
	private String			fOp;
	private SVExpr			fDelayExpr;
	private SVExpr			fRHS;
	
	public SVDBAssignStmt() {
		super(SVDBItemType.AssignStmt);
	}
	
	public void setLHS(SVExpr lhs) {
		fLHS = lhs;
	}
	
	public SVExpr getLHS() {
		return fLHS;
	}
	
	public void setOp(String op) {
		fOp = op;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public void setRHS(SVExpr expr) {
		fRHS = expr;
	}
	
	public SVExpr getRHS() {
		return fRHS;
	}
	
	public void setDelayExpr(SVExpr expr) {
		fDelayExpr = expr;
	}
	
	public SVExpr getDelayExpr() {
		return fDelayExpr;
	}

}
