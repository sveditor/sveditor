package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBModportDecl extends SVDBChildItem implements ISVDBChildParent {
	private List<SVDBModportItem>			fModportItemList;
	
	public SVDBModportDecl() {
		super(SVDBItemType.ModportDecl);
		fModportItemList = new ArrayList<SVDBModportItem>();
	}
	
	public List<SVDBModportItem> getModportItemList() {
		return fModportItemList;
	}
	
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fModportItemList.iterator();
			}
		};
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fModportItemList.add((SVDBModportItem)item);
	}

	public void addModportItem(SVDBModportItem item) {
		item.setParent(this);
		fModportItemList.add(item);
	}

}
