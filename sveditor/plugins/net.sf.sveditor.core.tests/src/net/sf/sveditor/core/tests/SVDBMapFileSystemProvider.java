package net.sf.sveditor.core.tests;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.index.ISVDBFileSystemChangeListener;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;

public class SVDBMapFileSystemProvider implements ISVDBFileSystemProvider {
	private Map<String, String>			fFileMap;
	
	private static class OutStream extends OutputStream {
		public ByteArrayOutputStream 	fBOS;
		public String					fPath;
		
		public OutStream(String path) {
			fBOS = new ByteArrayOutputStream();
			fPath = path;
		}

		@Override
		public void write(int b) throws IOException {
			fBOS.write(b);
		}
	}
	
	public SVDBMapFileSystemProvider(Map<String, String> fmap) {
		fFileMap = fmap;
	}
	
	public Map<String, String> getFileMap() {
		return fFileMap;
	}
	
	@Override
	public void init(String root) { }

	@Override
	public void dispose() { }

	@Override
	public void addMarker(String path, String type, int lineno, String msg) { }

	@Override
	public void clearMarkers(String path) { }

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
		// TODO: probably need to be 
		return false;
	}

	@Override
	public List<String> getFiles(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public InputStream openStream(String path) {
		if (fFileMap.containsKey(path)) {
			return new StringInputStream(fFileMap.get(path));
		} else {
			return null;
		}
	}

	@Override
	public OutputStream openStreamWrite(String path) {
		return new OutStream(path);
	}

	@Override
	public void closeStream(InputStream in) { }

	@Override
	public void closeStream(OutputStream out) { 
		if (out instanceof OutStream) {
			OutStream os = (OutStream)out;
			if (fFileMap.containsKey(os.fPath)) {
				fFileMap.remove(os.fPath);
			}
			fFileMap.put(os.fPath, os.fBOS.toString());
		}
	}

	@Override
	public long getLastModifiedTime(String path) {
		return 1;
	}

	@Override
	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) { }

	@Override
	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) { }

}
