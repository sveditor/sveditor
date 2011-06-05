package net.sf.sveditor.core.db;


public interface ISVDBChildItem extends ISVDBItemBase {
	
	ISVDBChildItem getParent();

	void setParent(ISVDBChildItem parent);
	
}
