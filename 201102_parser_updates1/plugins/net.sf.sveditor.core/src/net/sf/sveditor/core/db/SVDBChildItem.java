package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.attr.SVDBParentAttr;

public class SVDBChildItem extends SVDBItemBase implements ISVDBChildItem {
	@SVDBParentAttr
	private ISVDBChildItem 			fParent;
	
	public SVDBChildItem(SVDBItemType type) {
		super(type);
	}

	public ISVDBChildItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}
	
	public Iterable getChildren() {
		return EmptySVDBItemIterable.iterable;
	}
	
}
