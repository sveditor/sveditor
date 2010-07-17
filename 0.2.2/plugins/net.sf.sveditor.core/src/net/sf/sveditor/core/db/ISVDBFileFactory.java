package net.sf.sveditor.core.db;

import java.io.InputStream;

public interface ISVDBFileFactory {
	
	void init(InputStream in, String filename);
	
	SVDBFile parse(InputStream in, String filename);

}
