package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBVisitor;
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
	
	public SVDBExpr getInstName() {
		return fInstName;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_config_inst_clause_stmt(this);
	}
}
