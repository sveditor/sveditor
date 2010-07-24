package net.sf.sveditor.core.tests.content_assist;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;

public class FileIndexIterator implements ISVDBIndexIterator {
	Map<String, SVDBFile>			fFileMap;
	
	public FileIndexIterator(SVDBFile file) {
		fFileMap = new HashMap<String, SVDBFile>();
		fFileMap.put(file.getName(), file);
	}

	public ISVDBItemIterator<SVDBItem> getItemIterator() {
		return new SVDBIndexItemIterator(fFileMap);
	}

}
