package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBForkStmt extends SVDBStmt {
	public enum JoinType {
		Join,
		JoinNone,
		JoinAny
	};
	
	private List<SVDBStmt>				fStmtList;
	private JoinType					fJoinType;
	
	public SVDBForkStmt() {
		super(SVDBItemType.ForkStmt);
		fStmtList = new ArrayList<SVDBStmt>();
	}
	
	public List<SVDBStmt> getStmtList() {
		return fStmtList;
	}
	
	public void addStmt(SVDBStmt stmt) {
		fStmtList.add(stmt);
	}

	public JoinType getJoinType() {
		return fJoinType;
	}
	
	public void setJoinType(JoinType join_type) {
		fJoinType = join_type;
	}

}
