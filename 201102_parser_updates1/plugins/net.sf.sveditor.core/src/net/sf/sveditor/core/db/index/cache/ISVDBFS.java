package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.util.List;

public interface ISVDBFS {
	
	String getRoot();
	
	/**
	 * The FS provider must remove the path corresponding to itself
	 * from the supplied list. This is used by the database-compacting
	 * process
	 * 
	 * @param db_file_list
	 */
	void removeStoragePath(List<File> db_file_list);
	
	InputStream openFileRead(String path) throws IOException;
	
	RandomAccessFile openChannelRead(String path);
	
	void closeChannel(RandomAccessFile ch);
	
	void close(InputStream in);
	
	OutputStream openFileWrite(String path) throws IOException;
	
	RandomAccessFile openChannelWrite(String path);
	
	boolean fileExists(String path);
	
	long lastModified(String path);
	
	void delete(String path);
	
	void mkdirs(String path);
	
	void sync() throws IOException;

}
