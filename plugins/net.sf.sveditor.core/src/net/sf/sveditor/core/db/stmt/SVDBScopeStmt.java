package net.sf.sveditor.core.db.stmt;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBLocation;

public class SVDBScopeStmt extends SVDBStmt implements ISVDBScopeItem {
	
	public SVDBScopeStmt(SVDBStmtType type) {
		super(type);
	}

	public ISVDBScopeItem getParent() {
		// TODO Auto-generated method stub
		return null;
	}

	public void setParent(ISVDBScopeItem parent) {
		// TODO Auto-generated method stub

	}

	public String getName() {
		// TODO Auto-generated method stub
		return null;
	}

	public SVDBLocation getEndLocation() {
		// TODO Auto-generated method stub
		return null;
	}

	public void setEndLocation(SVDBLocation loc) {
		// TODO Auto-generated method stub

	}

	public List<ISVDBItemBase> getItems() {
		// TODO Auto-generated method stub
		return null;
	}

}
