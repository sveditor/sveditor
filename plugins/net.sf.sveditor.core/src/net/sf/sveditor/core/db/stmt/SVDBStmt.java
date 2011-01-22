package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBStmt extends SVDBItemBase {
	private ISVDBScopeItem				fParent;
	
	public SVDBStmt(SVDBStmtType type) {
		super(SVDBItemType.Stmt);
		
	}
	
	

}
