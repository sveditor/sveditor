package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBWhileStmt extends SVDBStmt {
	private SVDBExpr				fCond;
	private SVDBStmt			fBody;

	public SVDBWhileStmt() {
		super(SVDBItemType.WhileStmt);
	}
	
	public SVDBWhileStmt(SVDBExpr cond) {
		super(SVDBItemType.WhileStmt);
		fCond = cond;
		fBody = null;
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}
	
	public void setBody(SVDBStmt body) {
		fBody = body;
	}

}
