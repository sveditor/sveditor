package net.sf.sveditor.core.db;

public interface ISVDBChildItem extends ISVDBItemBase {
	
	ISVDBScopeItem getParent();

	void setParent(ISVDBScopeItem parent);


}
