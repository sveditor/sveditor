package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBIfStmt extends SVDBStmt {
	private SVDBExpr			fCondExpr;
	private SVDBStmt		fIfStmt;
	private SVDBStmt		fElseStmt;
	
	public SVDBIfStmt() {
		super(SVDBItemType.IfStmt);
	}
	
	public SVDBIfStmt(SVDBExpr expr) {
		super(SVDBItemType.IfStmt);
		fCondExpr = expr;
	}
	
	public SVDBExpr getCond() {
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
