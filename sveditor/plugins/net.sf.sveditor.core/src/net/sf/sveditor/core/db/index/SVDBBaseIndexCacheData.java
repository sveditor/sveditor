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


package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SVDBBaseIndexCacheData {
	
	public String									fVersion;
	public String									fBaseLocation;
	public List<String>								fIncludePathList;
	public List<String>								fMissingIncludeFiles;
	public Map<String, String>						fGlobalDefines;
	public Map<String, String>						fDefineMap;
	public Map<String, List<SVDBDeclCacheItem>>		fDeclCacheMap;
	public Map<String, List<SVDBDeclCacheItem>>		fPackageCacheMap;
	
	// Map between reference ids and file ids containing them
	public Map<String, List<Integer>>				fRefCache;
	
	// Contains cached information about each file
	public Map<String, SVDBRootFileCacheData>		fRootFileCacheData;
	public boolean									fForceSV;

	public SVDBBaseIndexCacheData(String base) {
		fBaseLocation = base;
		fIncludePathList = new ArrayList<String>();
		fMissingIncludeFiles = new ArrayList<String>();
		fGlobalDefines = new HashMap<String, String>();
		fDefineMap = new HashMap<String, String>();
		fDeclCacheMap = new HashMap<String, List<SVDBDeclCacheItem>>();
		fPackageCacheMap = new HashMap<String, List<SVDBDeclCacheItem>>();
		fRefCache = new HashMap<String, List<Integer>>();
		fRootFileCacheData = new HashMap<String, SVDBRootFileCacheData>();
	}
	
	public String getVersion() {
		return fVersion;
	}
	
	public void setVersion(String version) {
		fVersion = version;
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public void addMissingIncludeFile(String path) {
		if (!fMissingIncludeFiles.contains(path)) {
			fMissingIncludeFiles.add(path);
		}
	}
	
	public void clearMissingIncludeFiles() {
		fMissingIncludeFiles.clear();
	}
	
	public List<String> getMissingIncludeFiles() {
		return fMissingIncludeFiles;
	}
	
	public void setGlobalDefine(String key, String val) {
		if (fGlobalDefines.containsKey(key)) {
			fGlobalDefines.remove(key);
		}
		fGlobalDefines.put(key, val);
	}
	
	public Map<String, String> getGlobalDefines() {
		return fGlobalDefines;
	}
	
	public void clearGlobalDefines() {
		fGlobalDefines.clear();
	}

	public void clearDefines() {
		fDefineMap.clear();
		fDefineMap.putAll(fGlobalDefines);
	}
	
	public void addDefine(String key, String val) {
		if (fDefineMap.containsKey(key)) {
			fDefineMap.remove(key);
		}
		fDefineMap.put(key, val);
	}
	
	public Map<String, String> getDefines() {
		return fDefineMap;
	}
	
	public void clearIncludePaths() {
		fIncludePathList.clear();
	}
	
	public void addIncludePath(String path) {
		if (!fIncludePathList.contains(path)) {
			fIncludePathList.add(path);
		}
	}
	
	public List<String> getIncludePaths() {
		return fIncludePathList;
	}
	
	public Map<String, List<SVDBDeclCacheItem>> getDeclCacheMap() {
		return fDeclCacheMap;
	}
	
	public Map<String, List<SVDBDeclCacheItem>> getPackageCacheMap() {
		return fPackageCacheMap;
	}
	
	public Map<String, List<Integer>> getReferenceCacheMap() {
		return fRefCache;
	}
	
	public void clear() {
		fDeclCacheMap.clear();
	}
}
