package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBChildParent extends SVDBChildItem implements ISVDBChildParent {
	private List<ISVDBChildItem>			fItems;
	
	public SVDBChildParent(SVDBItemType type) {
		super(type);
		fItems = new ArrayList<ISVDBChildItem>();
	}

	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fItems.add(item);
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return fItems.iterator();
			}
		};
	}

}
