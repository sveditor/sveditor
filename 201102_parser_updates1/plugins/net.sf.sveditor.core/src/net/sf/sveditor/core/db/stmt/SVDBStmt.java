package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBStmt extends SVDBChildItem {
	
	protected SVDBStmt(SVDBItemType type) {
		super(type);
	}
	
	@Override
	public SVDBStmt duplicate() {
		SVDBStmt ret = new SVDBStmt(getType());
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
	}

	@Override
	public boolean equals(Object obj) {
		// TODO Auto-generated method stub
		return super.equals(obj);
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		// TODO Auto-generated method stub
		return super.equals(obj, full);
	}
	
	public static boolean isType(ISVDBItemBase item, SVDBItemType ... types) {
		// TODO: item.itemClass() == SVDBItemClass.Stmt
		boolean ret = true;
		
		if (ret) {
			ret = false;
			for (SVDBItemType t : types) {
				if (t == item.getType()) {
					ret = true;
					break;
				}
			}
		}
		
		return ret;
	}
	
}
