package net.sf.sveditor.core.tests;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

public class TestNullIndexCache implements ISVDBIndexCache {
	private Object						fData;
	private List<String>				fFileList;
	private Map<String, Long>			fLastModifiedMap;
	private Map<String, SVDBFile>		fPreProcFileMap;
	private Map<String, SVDBFile>		fFileMap;
	private Map<String, SVDBFileTree>	fFileTreeMap;
	
	public TestNullIndexCache() {
		fFileList = new ArrayList<String>();
		fLastModifiedMap = new HashMap<String, Long>();
		fPreProcFileMap = new HashMap<String, SVDBFile>();
		fFileMap = new HashMap<String, SVDBFile>();
		fFileTreeMap = new HashMap<String, SVDBFileTree>();
	}

	public void setIndexData(Object data) {
		fData = data;
	}

	public Object getIndexData() {
		return fData;
	}

	public void init(IProgressMonitor monitor, Object index_data) {
		fData = index_data;
	}

	public void clear() {
		fFileList.clear();
		fFileMap.clear();
		fFileTreeMap.clear();
		fLastModifiedMap.clear();
		fPreProcFileMap.clear();
	}

	public List<String> getFileList() {
		return fFileList;
	}

	public long getLastModified(String path) {
		if (fLastModifiedMap.containsKey(path)) {
			return fLastModifiedMap.get(path);
		} else {
			return -1;
		}
	}

	public void setLastModified(String path, long timestamp) {
		if (fLastModifiedMap.containsKey(path)) {
			fLastModifiedMap.remove(path);
		}
		fLastModifiedMap.put(path, timestamp);
	}

	public void addFile(String path) {
		if (!fFileList.contains(path)) {
			fFileList.add(path);
		}
	}

	public SVDBFile getPreProcFile(IProgressMonitor monitor, String path) {
		return fPreProcFileMap.get(path);
	}

	public void setPreProcFile(String path, SVDBFile file) {
		if (fPreProcFileMap.containsKey(path)) {
			fPreProcFileMap.remove(path);
		}
		fPreProcFileMap.put(path, file);
	}

	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path) {
		return fFileTreeMap.get(path);
	}

	public void setFileTree(String path, SVDBFileTree file) {
		if (fFileTreeMap.containsKey(path)) {
			fFileTreeMap.remove(path);
		}
		fFileTreeMap.put(path, file);
	}

	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		return fFileMap.get(path);
	}

	public void setFile(String path, SVDBFile file) {
		if (fFileMap.containsKey(path)) {
			fFileMap.remove(path);
		}
		fFileMap.put(path, file);
	}

	public void removeFile(String path) {
		fFileList.remove(path);
		fPreProcFileMap.remove(path);
		fFileMap.remove(path);
		fFileTreeMap.remove(path);
	}

	public void sync() {
		// TODO Auto-generated method stub

	}

}
