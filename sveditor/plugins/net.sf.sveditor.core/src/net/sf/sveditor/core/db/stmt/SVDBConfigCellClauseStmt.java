package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigCellClauseStmt extends SVDBConfigRuleStmtBase {
	
	public SVDBExpr					fCellId;
	
	public SVDBConfigCellClauseStmt() {
		super(SVDBItemType.ConfigCellClauseStmt);
	}
	
	public void setCellId(SVDBExpr id) {
		fCellId = id;
	}
	
	public SVDBExpr getCellId() {
		return fCellId;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_config_cell_clause_stmt(this);
	}

}
