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
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;

public class SVDBIndexCacheData implements ISVPreProcFileMapper {
	
	public String									fVersion;
	public String									fBaseLocation;
	public List<String>								fIncludePathList;
	public List<String>								fMissingIncludeFiles;
	public Map<String, String>						fGlobalDefines;
	public Map<String, String>						fDefineMap;

	// Map from file path to ID
	public Map<String, Integer>						fFilePathIdMap;
	
	// Map from file ID to path
	public Map<Integer, String>						fFileIdPathMap;

	// Current maximum file ID
	public int										fFileIdMax;
	
	// Contains cached information about each root file
	// - File ID
	// - File attributes
	// - Last timestamp
	public Map<Integer, SVDBFileCacheData>			fFileCacheData;

	// Indicates whether this index is processing files in
	// multi-file compilation unit mode. MFCU mode means that
	// macro definitions propagate across root files
	public boolean									fMFCU;

	public boolean									fForceSV;

	public SVDBIndexCacheData(String base) {
		fBaseLocation = base;
		fIncludePathList = new ArrayList<String>();
		fMissingIncludeFiles = new ArrayList<String>();
		fGlobalDefines = new HashMap<String, String>();
		fDefineMap = new HashMap<String, String>();
		fFilePathIdMap = new HashMap<String, Integer>();
		fFileIdPathMap = new HashMap<Integer, String>();
		fFileIdMax = 1;
		fFileCacheData = new HashMap<Integer, SVDBFileCacheData>();
	}
	
	public void initFileMapperState(SVDBIndexCacheData data) {
		fFilePathIdMap.clear();
		fFilePathIdMap.putAll(data.fFilePathIdMap);
		fFileIdPathMap.clear();
		fFileIdPathMap.putAll(data.fFileIdPathMap);
		fIncludePathList.clear();
		fIncludePathList.addAll(data.fIncludePathList);
	}
	
	public Map<Integer, SVDBFileCacheData> getRootFileCacheData() {
		return fFileCacheData;
	}
	
	public Collection<SVDBFileCacheData> getRootFilesCacheData() {
		return fFileCacheData.values();
	}
	
	public SVDBFileCacheData getFileCacheData(int id) {
		// Should we create if it doesn't exist?
		return fFileCacheData.get(id);
	}
	
	public SVDBFileCacheData getFileCacheData(String path) {
		if (fFilePathIdMap.containsKey(path)) {
			return fFileCacheData.get(fFilePathIdMap.get(path));
		}
		return null;
	}
	
	public void setFileCacheData(int id, SVDBFileCacheData cd) {
		fFileCacheData.remove(id);
		fFileCacheData.put(id, cd);
	}
	
	public Map<Integer, SVDBFileCacheData> getFileCacheData() {
		return fFileCacheData;
	}
	
	public void removeFileCacheData(String path) {
		if (fFilePathIdMap.containsKey(path)) {
			removeFileCacheData(fFilePathIdMap.get(path));
		}
	}
	
	public void removeFileCacheData(int id) {
		fFileCacheData.remove(id);
	}
	
	public void addFileCacheData(SVDBFileCacheData cd) {
		// Remove, just to be safe
		fFileCacheData.remove(cd.getFileId());
		fFileCacheData.put(cd.getFileId(), cd);
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
	
	public boolean containsFile(String path, int attr) {
		if ((attr & ISVDBDeclCacheFileAttr.FILE_ATTR_ARG_FILE) != 0 &&
				(attr & ISVDBDeclCacheFileAttr.FILE_ATTR_SRC_FILE) != 0) {
			System.out.println("Warning: containsFile - both ARG_FILE and SRC_FILE set");
		}
		if (fFilePathIdMap.containsKey(path)) {
			int id = fFilePathIdMap.get(path);
			SVDBFileCacheData file_info = fFileCacheData.get(id);
			if (file_info != null) {
				return ((attr & file_info.fFileAttr) == attr);
			}
		}
	
//		// If the path wasn't a root file, keep checking 
//		// if the caller indicates they want a broader result
//		if (attr == 0 || 
//				(attr & (ISVDBDeclCache.FILE_ATTR_SRC_FILE)) != 0) {
//			for (SVDBFileCacheData cd : fFileCacheData.values()) {
//				// Iterate through included files
//				for (cd.getIncludedFiles()) {
//					
//				}
//			}
//			
//		}
		
		return false;
	}

	/*** File Mapper API implementation */
	@Override
	public int mapFilePathToId(String path, boolean add) {
		int id = 0;
		
		if (fFilePathIdMap.containsKey(path)) {
			id = fFilePathIdMap.get(path);
		} else if (add) {
			for (int i=0; i<2; i++) {
				while (fFileIdMax<Integer.MAX_VALUE) {
					if (!fFileIdPathMap.containsKey(fFileIdMax)) {
						id = fFileIdMax;
						fFileIdPathMap.put(id, path);
						fFilePathIdMap.put(path, id);
						fFileCacheData.put(id, new SVDBFileCacheData(id, 0));
						fFileIdMax++;
						break;
					}
					fFileIdMax++;
				}
				
				if (id != 0) {
					break;
				}
				
				// Try again
				fFileIdMax = 1;
			}
			
			if (id == 0) {
				System.out.println("[Internal Error] Ran out of file IDs");
			}
		}
		
		return id;
	}

	@Override
	public String mapFileIdToPath(int id) {
		String path = fFileIdPathMap.get(id);
		
		if (path == null) {
			try {
				throw new Exception("id " + id + " resulted in null");
			} catch (Exception e) {
				e.printStackTrace();
			}
			for (Map.Entry<Integer, String> e : fFileIdPathMap.entrySet()) {
				System.out.println("  " + e.getKey() + " " + e.getValue());
			}
		}
		
		return path;
	}

	public SVDBFileCacheData addFile(String path, int attr) {
		int id = mapFilePathToId(path, true);
		
		if (!fFileCacheData.containsKey(id)) {
			fFileCacheData.put(id, new SVDBFileCacheData(id, attr));
		} else {
			fFileCacheData.get(id).setFileAttr(attr);
		}
		return fFileCacheData.get(id);
	}
	
	public int getFileAttr(String path) {
		int id = mapFilePathToId(path, false);
		if (id > 0) {
			return fFileCacheData.get(id).getFileAttr();
		}
			
		return 0;
	}
	
	public void setFileAttr(String path, int attr) {
		int id = mapFilePathToId(path, false);
		
		if (id > 0) {
			fFileCacheData.get(id).setFileAttr(attr);
		} else {
			// TODO: error
		}
	}
	
	public void setFileAttrBits(String path, int attr) {
		int id = mapFilePathToId(path, false);

		if (id > 0) {
			int ex_attr = fFileCacheData.get(id).getFileAttr();
			fFileCacheData.get(id).setFileAttr(ex_attr | attr);
		} else {
			// TODO: error
		}
	}
	
	public void clrFileAttrBits(String path, int attr) {
		int id = mapFilePathToId(path, false);

		if (id > 0) {
			int ex_attr = fFileCacheData.get(id).getFileAttr();
			ex_attr &= ~attr;
			fFileCacheData.get(id).setFileAttr(ex_attr);
		} else {
			// TODO: error
		}
	}
	
	public List<String> getFileList(int attr) {
		List<String> ret = new ArrayList<String>();
		
		for (SVDBFileCacheData cd : fFileCacheData.values()) {
			if ((cd.getFileAttr() & attr) == attr) {
				ret.add(mapFileIdToPath(cd.getFileId()));
			}
		}
		
		return ret;
	}
	
	public int getFileCount(int attr) {
		int ret = 0;
		for (SVDBFileCacheData cd : fFileCacheData.values()) {
			if ((cd.getFileAttr() & attr) == attr) {
				ret++;
			}
		}
		
		return ret;
	}
	

}
