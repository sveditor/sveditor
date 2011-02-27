package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBDoWhileStmt extends SVDBBodyStmt {
	private SVExpr			fCond;
	
	public SVDBDoWhileStmt() {
		super(SVDBItemType.DoWhileStmt);
	}
	
	public SVDBDoWhileStmt(ISVDBChildItem parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);
		
		fCond = SVExpr.readExpr(reader);
	}
	
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVExpr.writeExpr(fCond, writer);
	}

	public void setCond(SVExpr cond) {
		fCond = cond;
	}
	
	public SVExpr getCond() {
		return fCond;
	}
	
}
