package net.sf.sveditor.core.db;

import java.util.ArrayList;
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
	
	public void addModportItem(SVDBModportItem item) {
		fModportItemList.add(item);
	}

}
