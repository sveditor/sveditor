package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBForStmt extends SVDBBodyStmt {
	private SVDBStmt		fInitExpr;
	private SVExpr			fTestExpr;
	private SVExpr			fIncrExpr;
	
	public static void init() {
		SVDBPersistenceReader.registerPersistenceFactory(new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type,
					IDBReader reader) throws DBFormatException {
				return new SVDBForStmt(parent, type, reader);
			}
		}, SVDBItemType.ForStmt);
	}
	
	public SVDBForStmt() {
		super(SVDBItemType.ForStmt);
	}
	
	public SVDBForStmt(ISVDBChildItem parent, SVDBItemType stmt_type, IDBReader reader)
		throws DBFormatException {
		super(SVDBItemType.ForStmt);
		
		fInitExpr 	= SVDBStmt.readStmt(parent, reader);
		fTestExpr 	= SVExpr.readExpr(reader);
		fIncrExpr 	= SVExpr.readExpr(reader);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVDBStmt.writeStmt(fInitExpr, writer);
		SVExpr.writeExpr(fTestExpr, writer);
		SVExpr.writeExpr(fIncrExpr, writer);
	}
	
	public SVDBStmt getInitExpr() {
		return fInitExpr;
	}
	
	public void setInitStmt(SVDBStmt stmt) {
		fInitExpr = stmt;
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
