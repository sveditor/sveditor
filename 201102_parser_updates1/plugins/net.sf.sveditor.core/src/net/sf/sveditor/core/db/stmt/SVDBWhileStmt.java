package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public class SVDBWhileStmt extends SVDBStmt {
	private SVExpr				fCond;
	private SVDBStmt			fBody;
	
	public SVDBWhileStmt(SVExpr cond) {
		super(SVDBItemType.WhileStmt);
		fCond = cond;
		fBody = null;
	}
	
	public SVDBWhileStmt(ISVDBItemBase parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);
		fCond = SVExpr.readExpr(reader);
		fBody = SVDBStmt.readStmt(this, reader);
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}
	
	public void setBody(SVDBStmt body) {
		fBody = body;
	}

}
