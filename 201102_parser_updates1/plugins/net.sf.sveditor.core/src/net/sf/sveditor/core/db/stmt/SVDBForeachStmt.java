package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBForeachStmt extends SVDBBodyStmt {
	private SVExpr 			fCond;
	
	public SVDBForeachStmt() {
		super(SVDBItemType.ForeachStmt);
	}
	
	public void setCond(SVExpr cond) {
		fCond = cond;
	}
	
	public SVExpr getCond() {
		return fCond;
	}
	
	

}
