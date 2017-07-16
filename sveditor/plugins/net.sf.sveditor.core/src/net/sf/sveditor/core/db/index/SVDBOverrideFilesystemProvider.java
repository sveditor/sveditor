package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.StringInputStream;

public class SVDBOverrideFilesystemProvider implements ISVDBFileSystemProvider {
	
	private static class FileInfo {
		private String					fPath;
		private String					fContent;
		
		public FileInfo(String path, String content) {
			fPath = path;
			fContent = content;
		}
		
		public InputStream getContents() {
			return new StringInputStream(fContent);
		}
	}
	
	private Map<String, FileInfo>				fFileMap;
	private ISVDBFileSystemProvider				fFSProvider;
	
	public SVDBOverrideFilesystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileMap 	= new HashMap<String, FileInfo>();
		fFSProvider = fs_provider;
	}
	
	public SVDBOverrideFilesystemProvider() {
		this(null);
	}
	
	public void addFile(String path, String content) {
		if (fFileMap.containsKey(path)) {
			fFileMap.remove(path);
		}
		FileInfo fi = new FileInfo(path, content);
		fFileMap.put(path, fi);
	}

	@Override
	public void init(String root) {
		if (fFSProvider != null) {
			fFSProvider.init(root);
		}
	}

	@Override
	public void dispose() {
		if (fFSProvider != null) {
			fFSProvider.dispose();
		}
	}

	@Override
	public void addMarker(String path, String type, int lineno, String msg) {
		if (fFSProvider != null) {
			fFSProvider.addMarker(path, type, lineno, msg);
		}
	}

	@Override
	public void clearMarkers(String path) {
		if (fFSProvider != null) {
			fFSProvider.clearMarkers(path);
		}
	}

	@Override
	public String resolvePath(String path, String fmt) {
		return path;
	}

	@Override
	public boolean fileExists(String path) {
		return fFileMap.containsKey(path);
	}

	@Override
	public boolean isDir(String path) {
		for (String key : fFileMap.keySet()) {
			if (key.startsWith(path) && key.length() > path.length() &&
					key.charAt(path.length()) == '/') {
				return true;
			}
		}
		return false;
	}

	@Override
	public List<String> getFiles(String path) {
		List<String> ret = new ArrayList<String>();
		
		for (String key : fFileMap.keySet()) {
			if (key.startsWith(path) && key.length() > path.length() &&
					key.charAt(path.length()) == '/') {
				ret.add(key);
			}
		}
		
		return ret;
	}

	@Override
	public InputStream openStream(String path) {
		if (fFileMap.containsKey(path)) {
			return fFileMap.get(path).getContents();
		} else {
			return null;
		}
	}

	@Override
	public OutputStream openStreamWrite(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void closeStream(InputStream in) {
		// TODO Auto-generated method stub

	}

	@Override
	public void closeStream(OutputStream in) {
		// TODO Auto-generated method stub

	}

	@Override
	public long getLastModifiedTime(String path) {
		if (fFileMap.containsKey(path)) {
			// TODO:
			return 0;
		} else {
			return -1;
		}
	}

	@Override
	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		// TODO Auto-generated method stub

	}

}
