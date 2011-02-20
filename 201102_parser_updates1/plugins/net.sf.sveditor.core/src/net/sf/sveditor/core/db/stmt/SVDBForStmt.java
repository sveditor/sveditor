package net.sf.sveditor.core.db.stmt;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBForStmt extends SVDBStmt {
	private SVExpr			fInitExpr;
	private SVExpr			fTestExpr;
	private SVExpr			fIncrExpr;
	private SVDBStmt		fBodyStmt;
	
	public static void init() {
		SVDBStmt.registerPersistenceFactory(new ISVDBStmtPersistenceFactory() {
			public SVDBStmt readSVDBStmt(ISVDBChildItem parent, SVDBStmtType stmt_type,
					IDBReader reader) throws DBFormatException {
				return new SVDBForStmt(parent, stmt_type, reader);
			}
		}, SVDBStmtType.ForStmt);
	}
	
	public SVDBForStmt() {
		super(SVDBStmtType.ForStmt);
	}
	
	public SVDBForStmt(ISVDBItemBase parent, SVDBStmtType stmt_type, IDBReader reader)
		throws DBFormatException {
		super(SVDBStmtType.ForStmt);
		
		fInitExpr = SVExpr.readExpr(reader);
		fTestExpr = SVExpr.readExpr(reader);
		fIncrExpr = SVExpr.readExpr(reader);
		
		fBodyStmt = SVDBStmt.readStmt(this, reader);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVExpr.writeExpr(fInitExpr, writer);
		SVExpr.writeExpr(fTestExpr, writer);
		SVExpr.writeExpr(fIncrExpr, writer);
		
		SVDBStmt.writeStmt(fBodyStmt, writer);
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
	
	public SVDBStmt getBodyStmt() {
		return fBodyStmt;
	}
	
	public void setBodyStmt(SVDBStmt body) {
		fBodyStmt = body;
	}

	public SVDBForStmt duplicate() {
		SVDBForStmt ret = new SVDBForStmt();
		ret.init(this);
		
		return ret;
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
		
		if (o.fBodyStmt == null) {
			fBodyStmt = null;
		} else {
			fBodyStmt = o.fBodyStmt.duplicate();
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
			if (fInitExpr == null || o.getInitExpr() == null) {
				ret &= (fInitExpr == o.getInitExpr());
			} else {
				ret &= fInitExpr.equals(o.getInitExpr());
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
