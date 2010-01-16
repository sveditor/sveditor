package net.sf.sveditor.core.db.index;

import java.io.InputStream;

public interface ISVDBFileSystemProvider {
	
	void init(String root);
	
	void dispose();
	
	boolean fileExists(String path);
	
	InputStream openStream(String path);
	
	void closeStream(InputStream in);
	
	long getLastModifiedTime(String path);
	
	void addFileSystemChangeListener(ISVDBFileSystemChangeListener l);
	
	void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l);

}
