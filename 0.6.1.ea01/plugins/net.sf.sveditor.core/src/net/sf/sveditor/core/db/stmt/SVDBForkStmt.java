package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBForkStmt extends SVDBBlockStmt {
	public enum JoinType {
		Join,
		JoinNone,
		JoinAny
	};
	
	private JoinType					fJoinType;
	
	public SVDBForkStmt() {
		super(SVDBItemType.ForkStmt);
	}
	
	public JoinType getJoinType() {
		return fJoinType;
	}
	
	public void setJoinType(JoinType join_type) {
		fJoinType = join_type;
	}

}
