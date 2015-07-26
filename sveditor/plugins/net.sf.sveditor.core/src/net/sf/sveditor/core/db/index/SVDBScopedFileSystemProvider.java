package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

public class SVDBScopedFileSystemProvider extends SVDBFSFileSystemProvider {
	private File					fRoot;
	private String					fRootParent;

	@Override
	public void init(String root) { 
		fRoot = new File(root);
		fRootParent = fRoot.getParent().replace('\\', '/');
	}

	@Override
	public List<String> getFiles(String path) {
		List<String> ret = null;
		
		if (path.equals("/")) {
			ret = new ArrayList<String>();
			ret.add("/" + fRoot.getName());
		} else {
			String effective_path = fRootParent + path;

			ret = super.getFiles(effective_path);

			// Trim path
			String prefix = fRootParent;
			for (int i=0; i<ret.size(); i++) {
				String p = ret.get(i).substring(prefix.length());
				ret.set(i, p);
			}
		}
		
		return ret;
	}
	

	@Override
	public boolean fileExists(String path) {
		String effective_path = fRootParent + path;
		return super.fileExists(effective_path);
	}

	@Override
	public boolean isDir(String path) {
		String effective_path = fRootParent + path;
		return super.isDir(effective_path);
	}

	public InputStream openStream(String path) {
		String effective_path = fRootParent + path;
		return super.openStream(effective_path);
	}

	@Override
	public OutputStream openStreamWrite(String path) {
		String effective_path = fRootParent + path;
		return super.openStreamWrite(effective_path);
	}

	@Override
	public long getLastModifiedTime(String path) {
		String effective_path = fRootParent + path;
		return super.getLastModifiedTime(effective_path);
	}

}
