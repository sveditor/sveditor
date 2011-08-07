package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAssertStmt extends SVDBStmt {
	private SVDBExpr				fExpr;
	private SVDBActionBlockStmt		fActionBlock;
	
	public SVDBAssertStmt() {
		this(SVDBItemType.AssertStmt);
	}
	
	protected SVDBAssertStmt(SVDBItemType type) {
		super(type);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setActionBlock(SVDBActionBlockStmt stmt) {
		fActionBlock = stmt;
	}
	
	public SVDBActionBlockStmt getActionBlock() {
		return fActionBlock;
	}

}
