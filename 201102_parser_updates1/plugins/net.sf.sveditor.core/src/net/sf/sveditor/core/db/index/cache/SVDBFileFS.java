package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.util.List;

public class SVDBFileFS implements ISVDBFS {
	private class BlockBitmap {
		private MappedByteBuffer		fBlock;
		
		BlockBitmap(MappedByteBuffer block) {
			fBlock = block;
		}
		
	}
	
	private List<BlockBitmap>		fBlockBitmapList;
	
	
	public SVDBFileFS() {
		RandomAccessFile f;
//		f.getChannel().map(arg0, arg1, arg2)
	}
	
	public String getRoot() {
		return "";
	}

	public void removeStoragePath(List<File> db_file_list) {
		// TODO Auto-generated method stub
		
	}

	public InputStream openFileRead(String path) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}
	
	public RandomAccessFile openChannelRead(String path) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public RandomAccessFile openChannelWrite(String path) {
		return null;
	}
	
	public void closeChannel(RandomAccessFile ch) {
	}

	public void close(InputStream in) {
		// TODO Auto-generated method stub
		
	}

	public long lastModified(String path) {
		// TODO Auto-generated method stub
		return 0;
	}


	public OutputStream openFileWrite(String path) throws IOException {
		// TODO Auto-generated method stub
		return null;
	}


	public boolean fileExists(String path) {
		// TODO Auto-generated method stub
		return false;
	}


	public void sync() throws IOException {
		// TODO Auto-generated method stub
		
	}


	public void delete(String path) {
		// TODO Auto-generated method stub
		
	}

	public void mkdirs(String path) {
		
	}
	
}
