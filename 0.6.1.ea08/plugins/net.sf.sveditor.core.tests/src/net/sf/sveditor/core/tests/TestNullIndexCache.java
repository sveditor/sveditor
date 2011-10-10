/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

import org.eclipse.core.runtime.IProgressMonitor;

public class TestNullIndexCache implements ISVDBIndexCache {
	private Object						fData;
	private List<String>				fFileList;
	private Map<String, Long>			fLastModifiedMap;
	private Map<String, SVDBFile>		fPreProcFileMap;
	private Map<String, SVDBFile>		fFileMap;
	private Map<String, SVDBFileTree>	fFileTreeMap;
	private Map<String, List<SVDBMarker>>	fMarkerMap;
	
	public TestNullIndexCache() {
		fFileList = new ArrayList<String>();
		fLastModifiedMap = new HashMap<String, Long>();
		fPreProcFileMap = new HashMap<String, SVDBFile>();
		fFileMap = new HashMap<String, SVDBFile>();
		fFileTreeMap = new HashMap<String, SVDBFileTree>();
		fMarkerMap = new HashMap<String, List<SVDBMarker>>();
	}
	
	public void removeStoragePath(List<File> db_path_list) {}

	public void setIndexData(Object data) {
		fData = data;
	}

	public Object getIndexData() {
		return fData;
	}

	public boolean init(IProgressMonitor monitor, Object index_data) {
		fData = index_data;
		return true;
	}
	
	public void initLoad(IProgressMonitor monitor) {
	}

	public void clear() {
		fFileList.clear();
		fFileMap.clear();
		fFileTreeMap.clear();
		fLastModifiedMap.clear();
		fPreProcFileMap.clear();
		fMarkerMap.clear();
	}

	public List<String> getFileList() {
		return fFileList;
	}
	
	public List<SVDBMarker> getMarkers(String path) {
		return fMarkerMap.get(path);
	}

	public void setMarkers(String path, List<SVDBMarker> markers) {
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
