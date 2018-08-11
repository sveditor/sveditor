package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBConfigDefaultClauseStmt extends SVDBConfigRuleStmtBase {
	
	public SVDBConfigDefaultClauseStmt() {
		super(SVDBItemType.ConfigDefaultClauseStmt);
		fIsLibList = true;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_config_default_clause_stmt(this);
	}

}
