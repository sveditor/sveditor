package net.sf.sveditor.core.db.index.cache;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public interface ISVDBFS {
	
	InputStream openFileRead(String path) throws IOException;
	
	void close(InputStream in);
	
	OutputStream openFileWrite(String path) throws IOException;
	
	boolean fileExists(String path);
	
	long lastModified(String path);
	
	void delete(String path);
	
	void mkdirs(String path);
	
	void sync() throws IOException;

}
