package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.index.ISVDBIndex;

public class SVDBSearchResult<T> {
	private T						fItem;
	private ISVDBIndex				fIndex;
	
	public SVDBSearchResult(T item, ISVDBIndex index) {
		fItem  = item;
		fIndex = index;
	}
	
	public T getItem() {
		return fItem;
	}
	
	public ISVDBIndex getIndex() {
		return fIndex;
	}

}
