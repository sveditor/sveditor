package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBWaitForkStmt extends SVDBWaitStmt {
	
	public SVDBWaitForkStmt() {
		super(SVDBItemType.WaitForkStmt);
	}

}
