package net.sf.sveditor.core.db.index;

public interface ISVDBItemIterator<T> {
	
	boolean hasNext();
	
	T nextItem();

}
