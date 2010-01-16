package net.sf.sveditor.core.db.index;

import java.util.List;

public interface ISVDBIndexList extends ISVDBIndex {
	
	void addIndex(ISVDBIndex idx);
	
	void removeIndex(ISVDBIndex idx);
	
	List<ISVDBIndex> getIndexList();
	
}
