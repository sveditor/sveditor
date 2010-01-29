package net.sf.sveditor.core.indent;

import java.util.List;

public class SVIndentStmt {
	protected List<SVIndentStmt>			fStmtList;
	protected SVIndentStmtType				fType;
	
	public SVIndentStmt(SVIndentStmtType type) {
		fType = type;
	}
	
	public SVIndentStmtType getType() {
		return fType;
	}

}
