package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBForStmt extends SVDBBodyStmt {
	private SVDBStmt		fInitExpr;
	private SVDBExpr			fTestExpr;
	private SVDBExpr			fIncrExpr;
	
	public SVDBForStmt() {
		super(SVDBItemType.ForStmt);
	}
	
	public SVDBStmt getInitExpr() {
		return fInitExpr;
	}
	
	public void setInitStmt(SVDBStmt stmt) {
		fInitExpr = stmt;
	}
	
	public SVDBExpr getTestExpr() {
		return fTestExpr;
	}
	
	public void setTestExpr(SVDBExpr expr) {
		fTestExpr = expr;
	}
	
	public SVDBExpr getIncrExpr() {
		return fIncrExpr;
	}
	
	public void setIncrExpr(SVDBExpr expr) {
		fIncrExpr = expr;
	}
	
	public SVDBForStmt duplicate() {
		return (SVDBForStmt)super.duplicate();
	}
	
	public void init(ISVDBItemBase other) {
		super.init(other);
		
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
		
		if (!super.equals(obj, full)) {
			return false;
		}
		
		if (!(obj instanceof SVDBForStmt)) {
			return false;
		}
		
		SVDBForStmt o = (SVDBForStmt)obj;
		boolean ret = true;
		
		if (full) {
			if (fInitExpr == null || o.fInitExpr == null) {
				ret &= (fInitExpr == o.fInitExpr);
			} else {
				ret &= fInitExpr.equals(o.fInitExpr);
			}
			
			if (fTestExpr == null || o.getTestExpr() == null) {
				ret &= (fTestExpr == o.getTestExpr());
			} else {
				ret &= fTestExpr.equals(o.getTestExpr());
			}
			
			if (fIncrExpr == null || o.getIncrExpr() == null) {
				ret &= (fIncrExpr == o.getIncrExpr());
			} else {
				ret &= fIncrExpr.equals(o.getIncrExpr());
			}
		} 
		
		return ret;
	}
	
}
