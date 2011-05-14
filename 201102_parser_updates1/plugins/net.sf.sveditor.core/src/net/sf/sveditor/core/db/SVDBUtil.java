package net.sf.sveditor.core.db;

import java.util.Iterator;

public class SVDBUtil {
	
	public static int getChildrenSize(ISVDBChildParent p) {
		int count=0;
		Iterator<ISVDBChildItem> it = p.getChildren().iterator();
		while (it.hasNext()) {
			count++;
			it.next();
		}
		return count;
	}
	
	public static void addAllChildren(ISVDBChildParent dest, ISVDBChildParent src) {
		for (ISVDBChildItem c : src.getChildren()) {
			dest.addChildItem(c);
		}
	}

}
