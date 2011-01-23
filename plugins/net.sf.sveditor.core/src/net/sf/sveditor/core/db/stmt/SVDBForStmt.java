package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBForStmt extends SVDBScopeStmt {
	private SVExpr			fInitExpr;
	private SVExpr			fTestExpr;
	private SVExpr			fIncrExpr;
	
	public SVDBForStmt() {
		super(SVDBStmtType.ForStmt);
	}
	
	public SVExpr getInitExpr() {
		return fInitExpr;
	}
	
	public void setInitExpr(SVExpr expr) {
		fInitExpr = expr;
	}
	
	public SVExpr getTestExpr() {
		return fTestExpr;
	}
	
	public void setTestExpr(SVExpr expr) {
		fTestExpr = expr;
	}
	
	public SVExpr getIncrExpr() {
		return fIncrExpr;
	}
	
	public void setIncrExpr(SVExpr expr) {
		fIncrExpr = expr;
	}

	public SVDBForStmt duplicate() {
		SVDBForStmt ret = new SVDBForStmt();
		ret.init(this);
		
		return ret;
	}
	
	public void init(ISVDBItemBase other) {
//		super.init(other);
		
		SVDBForStmt o = (SVDBForStmt)other;
		if (o.fIncrExpr != null) {
			fIncrExpr = o.fIncrExpr.duplicate();
		} else {
			fIncrExpr = null;
		}
		
		if (o.fTestExpr != null) {
			fTestExpr = o.fTestExpr.duplicate();
		} else {
			fTestExpr = null;
		}
		
		if (o.fInitExpr != null) {
			fInitExpr = o.fInitExpr.duplicate();
		} else {
			fInitExpr = null;
		}
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		
		// TODO Auto-generated method stub
		return super.equals(obj, full);
	}
	
}
