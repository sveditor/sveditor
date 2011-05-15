package net.sf.sveditor.core.db;


public interface ISVDBChildParent extends ISVDBChildItem, ISVDBAddChildItem {
	
	Iterable<ISVDBChildItem> getChildren();

}
