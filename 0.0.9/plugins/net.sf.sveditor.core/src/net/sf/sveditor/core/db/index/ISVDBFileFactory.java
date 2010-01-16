package net.sf.sveditor.core.db.index;

import java.io.InputStream;

import net.sf.sveditor.core.db.SVDBFile;

public interface ISVDBFileFactory {
	
	SVDBFile parse(InputStream in, String path);
	
}
