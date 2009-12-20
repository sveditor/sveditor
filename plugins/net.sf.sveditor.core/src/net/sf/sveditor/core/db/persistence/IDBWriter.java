package net.sf.sveditor.core.db.persistence;

import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public interface IDBWriter {
	
	void writeInt(int val);
	
	void writeLong(long val);
	
	void writeByteArray(byte data[]);
	
	void writeString(String val);
	
	void writeItemType(SVDBItemType type);
	
	@SuppressWarnings("unchecked")
	void writeItemList(Collection items);
	
	void writeStringList(List<String> items);
	
	void writeIntList(List<Integer> items);
	
}
