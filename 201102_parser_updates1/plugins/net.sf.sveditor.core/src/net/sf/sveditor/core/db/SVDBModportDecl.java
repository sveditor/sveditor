package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBModportDecl extends SVDBChildItem {
	private List<SVDBModportItem>			fModportItemList;
	
	public SVDBModportDecl() {
		super(SVDBItemType.ModportDecl);
		fModportItemList = new ArrayList<SVDBModportItem>();
	}
	
	public List<SVDBModportItem> getModportItemList() {
		return fModportItemList;
	}
	
	@Override
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator<ISVDBChildItem>)(Iterable)fModportItemList.iterator();
			}
		};
	}

	public void addModportItem(SVDBModportItem item) {
		fModportItemList.add(item);
	}

}
