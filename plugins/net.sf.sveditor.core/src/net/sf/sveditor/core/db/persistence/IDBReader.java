package net.sf.sveditor.core.db.persistence;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;

public interface IDBReader {
	
	int readInt() throws DBFormatException;
	
	long readLong() throws DBFormatException;
	
	byte [] readByteArray() throws DBFormatException;
	
	String readString() throws DBFormatException;
	
	SVDBItemType readItemType() throws DBFormatException;
	
	@SuppressWarnings("unchecked")
	List readItemList(SVDBFile file, SVDBScopeItem parent) throws DBFormatException;
	
	List<String> readStringList() throws DBFormatException;
	
	List<Integer> readIntList() throws DBFormatException;

}
