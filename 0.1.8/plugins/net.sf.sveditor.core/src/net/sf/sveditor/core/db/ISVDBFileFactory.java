package net.sf.sveditor.core.db;

import java.io.InputStream;

public interface ISVDBFileFactory {
	
	SVDBFile parse(InputStream in, String filename);

}
