package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAssignStmt extends SVDBStmt {
	private SVDBExpr			fLHS;
	private String			fOp;
	private SVDBExpr			fDelayExpr;
	private SVDBExpr			fRHS;
	
	public SVDBAssignStmt() {
		super(SVDBItemType.AssignStmt);
	}
	
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	
	public void setOp(String op) {
		fOp = op;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public void setRHS(SVDBExpr expr) {
		fRHS = expr;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
	
	public void setDelayExpr(SVDBExpr expr) {
		fDelayExpr = expr;
	}
	
	public SVDBExpr getDelayExpr() {
		return fDelayExpr;
	}

}
