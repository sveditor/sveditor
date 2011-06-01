package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;

public interface ISVDBBodyStmt extends ISVDBChildItem {
	
	SVDBStmt getBody();
	
	void setBody(SVDBStmt stmt);

}
