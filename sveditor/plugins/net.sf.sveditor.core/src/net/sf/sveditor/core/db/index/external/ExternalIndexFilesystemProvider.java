package net.sf.sveditor.core.db.index.external;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.List;

import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;

public class ExternalIndexFilesystemProvider extends SVDBFSFileSystemProvider {
	
	public ExternalIndexFilesystemProvider() {
		// TODO: need access to the comm endpoint that talks with the server
	}

	@Override
	public boolean fileExists(String path) {
		// TODO Auto-generated method stub
		return super.fileExists(path);
	}

	@Override
	public boolean isDir(String path) {
		// TODO Auto-generated method stub
		return super.isDir(path);
	}

	@Override
	public List<String> getFiles(String path) {
		// TODO Auto-generated method stub
		return super.getFiles(path);
	}

	@Override
	public long getLastModifiedTime(String path) {
		// TODO Auto-generated method stub
		return super.getLastModifiedTime(path);
	}

	@Override
	public String resolvePath(String path, String fmt) {
		// TODO Auto-generated method stub
		return super.resolvePath(path, fmt);
	}

	@Override
	public InputStream openStream(String path) {
		// TODO Auto-generated method stub
		return super.openStream(path);
	}

	@Override
	public OutputStream openStreamWrite(String path) {
		// TODO Auto-generated method stub
		return super.openStreamWrite(path);
	}


}
