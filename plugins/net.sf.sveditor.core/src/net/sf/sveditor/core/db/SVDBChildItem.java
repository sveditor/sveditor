package net.sf.sveditor.core.db;

public class SVDBChildItem extends SVDBItemBase implements ISVDBChildItem {
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
	
	public Iterable<ISVDBItemBase> getChildren() {
		return EmptySVDBItemIterable.iterable;
	}
	
}
