package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBActionBlockStmt extends SVDBStmt implements ISVDBAddChildItem {
	private int						fAddIdx;
	
	public SVDBStmt					fStmt;
	public SVDBStmt					fElseStmt;
	
	public SVDBActionBlockStmt() {
		super(SVDBItemType.ActionBlockStmt);
	}
	
	public void setStmt(SVDBStmt stmt) {
		fStmt = stmt;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}
	
	public void setElseStmt(SVDBStmt stmt) {
		fElseStmt = stmt;
	}
	
	public SVDBStmt getElseStmt() {
		return fElseStmt;
	}

	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx++ == 0) {
			fStmt = (SVDBStmt)item;
		} else if (fAddIdx++ == 1) {
			fStmt = (SVDBStmt)item;
		}
	}

}
