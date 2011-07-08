package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.utils.SVDBSingleItemIterable;

public class SVDBBodyStmt extends SVDBStmt implements ISVDBBodyStmt, ISVDBAddChildItem, ISVDBChildParent {
	private SVDBStmt			fBody;
	
	@SVDBDoNotSaveAttr
	private int					fAddIdx;
	
	protected SVDBBodyStmt(SVDBItemType stmt_type) {
		super(stmt_type);
	}
	
	public void setBody(SVDBStmt stmt) {
		fBody = stmt;
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return new SVDBSingleItemIterable<ISVDBChildItem>(fBody);
	}

	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx++ == 0) {
			fBody = (SVDBStmt)item;
			if (fBody != null) {
				fBody.setParent(this);
			}
		}
	}

}
