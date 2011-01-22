package net.sf.sveditor.core.db;

public class SVDBChildItem extends SVDBItemBase implements ISVDBChildItem {
	private ISVDBScopeItem 			fParent;
	
	public SVDBChildItem(SVDBItemType type) {
		super(type);
	}

	public ISVDBScopeItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBScopeItem parent) {
		fParent = parent;
	}
	
}
