package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBBodyStmt extends SVDBStmt {
	private SVDBStmt			fBody;
	
	public SVDBBodyStmt(SVDBItemType stmt_type) {
		super(stmt_type);
	}
	
	public SVDBBodyStmt(ISVDBChildItem parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVDBStmt.writeStmt(fBody, writer);
	}

	public void setBody(SVDBStmt stmt) {
		fBody = stmt;
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}
}
