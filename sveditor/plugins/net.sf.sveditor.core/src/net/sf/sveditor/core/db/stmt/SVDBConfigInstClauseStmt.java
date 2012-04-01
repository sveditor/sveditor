package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigInstClauseStmt extends SVDBConfigRuleStmtBase {
	
	public SVDBExpr		fInstName;
	
	public SVDBConfigInstClauseStmt() {
		super(SVDBItemType.ConfigInstClauseStmt);
	}
	
	public void setInstName(SVDBExpr inst) {
		fInstName = inst;
	}

}
