package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBConfigDefaultClauseStmt extends SVDBConfigRuleStmtBase {
	
	public SVDBConfigDefaultClauseStmt() {
		super(SVDBItemType.ConfigDefaultClauseStmt);
		fIsLibList = true;
	}

}
