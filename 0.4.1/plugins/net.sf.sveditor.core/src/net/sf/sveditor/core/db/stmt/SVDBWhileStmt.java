package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;

public class SVDBWhileStmt extends SVDBStmt {
	private SVExpr				fCond;
	private SVDBStmt			fBody;
	
	public SVDBWhileStmt(SVExpr cond) {
		super(SVDBStmtType.WhileStmt);
		fCond = cond;
		fBody = null;
	}
	
	public SVDBWhileStmt(ISVDBItemBase parent, SVDBStmtType stmt_type, IDBReader reader) throws DBFormatException {
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
