package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBIfStmt extends SVDBStmt {
	private SVExpr			fCondExpr;
	private SVDBStmt		fIfStmt;
	private SVDBStmt		fElseStmt;
	
	public SVDBIfStmt(SVExpr expr) {
		super(SVDBItemType.IfStmt);
		fCondExpr = expr;
	}
	
	public SVDBIfStmt(ISVDBItemBase parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);
		
		fCondExpr = SVExpr.readExpr(reader);
		fIfStmt = SVDBStmt.readStmt(this, reader);
		fElseStmt = SVDBStmt.readStmt(this, reader);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVExpr.writeExpr(fCondExpr, writer);
		SVDBStmt.writeStmt(fIfStmt, writer);
		SVDBStmt.writeStmt(fElseStmt, writer);
	}

	public SVExpr getCond() {
		return fCondExpr;
	}
	
	public SVDBStmt getIfStmt() {
		return fIfStmt;
	}
	
	public void setIfStmt(SVDBStmt stmt) {
		fIfStmt = stmt;
	}
	
	public SVDBStmt getElseStmt() {
		return fElseStmt;
	}
	
	public void setElseStmt(SVDBStmt stmt) {
		fElseStmt = stmt;
	}
	
	@Override
	public SVDBStmt duplicate() {
		SVDBIfStmt ret = new SVDBIfStmt(null);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		SVDBIfStmt o = (SVDBIfStmt)other;
		
		if (o.fCondExpr != null) {
			fCondExpr = o.fCondExpr.duplicate();
		} else {
			fCondExpr = null;
		}
		
		if (o.fIfStmt != null) {
			fIfStmt = o.fIfStmt.duplicate();
		} else {
			fIfStmt = null;
		}
		
		if (o.fElseStmt != null) {
			fElseStmt = o.fElseStmt.duplicate();
		} else {
			fElseStmt = null;
		}

		super.init(other);
	}
	
}
