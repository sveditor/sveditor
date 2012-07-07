package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.RandomAccessFile;

public class BufferedRandomAccessFileWriter extends RandomAccessFile {

	public BufferedRandomAccessFileWriter(File path) throws FileNotFoundException {
		super(path, "rw");
	}
	
	
}
