package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBRepeatStmt extends SVDBBodyStmt {
	
	private SVExpr				fRepeatExpr;


	public SVDBRepeatStmt() {
		super(SVDBItemType.RepeatStmt);
	}
	
	public SVDBRepeatStmt(ISVDBChildItem parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);
		fRepeatExpr = SVExpr.readExpr(reader);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);

		SVExpr.writeExpr(fRepeatExpr, writer);
	}

	public void setExpr(SVExpr expr) {
		fRepeatExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fRepeatExpr;
	}
	
}
