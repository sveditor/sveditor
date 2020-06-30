/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.index.cache;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;

public class InMemoryIndexCache implements ISVDBIndexCache {
	private Object							fData;
	private ISVDBIndexCacheMgr				fCacheMgr;
	private Set<String>						fFileList;
	private Set<String>						fArgFileList;
	private Map<String, Long>				fLastModifiedMap;
	private Map<String, SVDBFile>			fPreProcFileMap;
	private Map<String, SVDBFile>			fFileMap;
	private Map<String, SVDBFile>			fArgFileMap;
	private Map<String, SVDBFileTree>		fFileTreeMap;
	private Map<String, SVDBFileTree>		fArgFileTreeMap;
	private Map<String, List<SVDBMarker>>	fMarkerMap;
	
	public InMemoryIndexCache() {
		this(new InMemoryIndexCacheMgr());
	}
	
	public InMemoryIndexCache(ISVDBIndexCacheMgr mgr) {
		fCacheMgr = mgr;
		fFileList = new HashSet<String>();
		fArgFileList = new HashSet<String>();
		fLastModifiedMap = new HashMap<String, Long>();
		fPreProcFileMap = new HashMap<String, SVDBFile>();
		fFileMap = new HashMap<String, SVDBFile>();
		fArgFileMap = new HashMap<String, SVDBFile>();
		fFileTreeMap = new HashMap<String, SVDBFileTree>();
		fArgFileTreeMap = new HashMap<String, SVDBFileTree>();
		fMarkerMap = new HashMap<String, List<SVDBMarker>>();
	}
	
	public ISVDBIndexCacheMgr getCacheMgr() {
		return fCacheMgr;
	}

	public void dispose() { }

	public void removeStoragePath(List<File> db_path_list) {}
	
	public void setIndexData(Object data) {
		fData = data;
	}

	public Object getIndexData() {
		return fData;
	}

	public boolean init(IProgressMonitor monitor, Object index_data, String base_location) {
		fData = index_data;
		return true;
	}
	
	public void initLoad(IProgressMonitor monitor) {
	}

	public void clear(IProgressMonitor monitor) {
		
		monitor.beginTask("Clear Cache", 1);
		fFileList.clear();
		fArgFileList.clear();
		fFileMap.clear();
		fFileTreeMap.clear();
		fArgFileTreeMap.clear();
		fLastModifiedMap.clear();
		fPreProcFileMap.clear();
		fMarkerMap.clear();
		monitor.done();
	}

	public Set<String> getFileList(boolean is_argfile) {
		if (is_argfile) {
			return fArgFileList;
		} else {
			Set<String> ret = new HashSet<String>();
			// The filelist is the union
			for (String f : fFileList) {
				if (!ret.contains(f)) {
					ret.add(f);
				}
			}
			for (String f : fFileMap.keySet()) {
				if (!ret.contains(f)) {
					ret.add(f);
				}
			}
			for (String f : fPreProcFileMap.keySet()) {
				if (!ret.contains(f)) {
					ret.add(f);
				}
			}
			for (String f : fFileTreeMap.keySet()) {
				if (!ret.contains(f)) {
					ret.add(f);
				}
			}
			return ret;
		}
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		return fMarkerMap.get(path);
	}

	public void setMarkers(String path, List<SVDBMarker> markers, boolean is_argfile) {
		if (fMarkerMap.containsKey(path)) {
			fMarkerMap.remove(path);
		}
		fMarkerMap.put(path, markers);
	}

	public long getLastModified(String path) {
		if (fLastModifiedMap.containsKey(path)) {
			return fLastModifiedMap.get(path);
		} else {
			return -1;
		}
	}

	public void setLastModified(String path, long timestamp, boolean is_argfile) {
		if (fLastModifiedMap.containsKey(path)) {
			fLastModifiedMap.remove(path);
		}
		fLastModifiedMap.put(path, timestamp);
	}

	public void addFile(String path, boolean is_argfile) {
		if (is_argfile) {
			if (!fArgFileList.contains(path)) {
				fArgFileList.add(path);
			}
		} else {
			if (!fFileList.contains(path)) {
				fFileList.add(path);
			}
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

	public SVDBFileTree getFileTree(IProgressMonitor monitor, String path, boolean is_argfile) {
		if (is_argfile) {
			return fArgFileTreeMap.get(path);
		} else {
			return fFileTreeMap.get(path);
		}
	}

	public void setFileTree(String path, SVDBFileTree file, boolean is_argfile) {
		if (is_argfile) {
			if (fArgFileTreeMap.containsKey(path)) {
				fArgFileTreeMap.remove(path);
			}
			fArgFileTreeMap.put(path, file);
		} else {
			if (fFileTreeMap.containsKey(path)) {
				fFileTreeMap.remove(path);
			}
			fFileTreeMap.put(path, file);
		}
	}

	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		return fFileMap.get(path);
	}

	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		if (is_argfile) {
			if (fArgFileMap.containsKey(path)) {
				fArgFileMap.remove(path);
			}
			fArgFileMap.put(path, file);
		} else {
			if (fFileMap.containsKey(path)) {
				fFileMap.remove(path);
			}
			fFileMap.put(path, file);
		}
	}

	public void removeFile(String path, boolean is_argfile) {
		if (is_argfile) {
			fArgFileMap.remove(path);
		} else {
			fFileList.remove(path);
			fPreProcFileMap.remove(path);
			fFileMap.remove(path);
			fFileTreeMap.remove(path);			
		}
	}
	
	public Map<Integer, SVDBFile> getSubFileMap(String path) {
		// Unsupported
		return null;
	}

	public void setSubFileMap(String path, Map<Integer, SVDBFile> map) {
		// Unsupported
	}

	// Not supported...
	public FileType getFileType(String path) {
		return FileType.Invalid;
	}

	public void sync() {
		// TODO Auto-generated method stub

	}

	public Set<String> getArgFileList() {
		return fArgFileMap.keySet();
	}

	public SVDBFile getArgFile(IProgressMonitor monitor, String path) {
		return fArgFileMap.get(path);
	}

	public void setArgFile(String path, SVDBFile file) {
		if (fArgFileMap.containsKey(path)) {
			fArgFileMap.remove(path);
		}
		if (file != null) {
			fArgFileMap.put(path, file);
		}
	}

	public void removeArgFile(String path) {
		fArgFileMap.remove(path);
	}
	
}
