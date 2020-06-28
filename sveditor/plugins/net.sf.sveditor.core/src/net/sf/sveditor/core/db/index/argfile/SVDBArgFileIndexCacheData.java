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


package net.sf.sveditor.core.db.index.argfile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBRootFileCacheData;

/**
 * Collects data about an index that should be saved in the cache.
 * <ul>
 * <li>Root source files (from the parsed argument file tree)</li>
 * <li>Library files</li>
 * <li>Parse settings, such as MFCU</li>
 * <ul>
 * @author ballance
 *
 */
public class SVDBArgFileIndexCacheData extends SVDBBaseIndexCacheData {
	
	public List<String>						fArgFilePaths;
	public List<Integer>					fArgFileAttr;
	public List<Long>						fArgFileTimestamps;
	public List<SVDBFile>					fArgFiles = new ArrayList<SVDBFile>();
	
	// List of the library files
	public List<String>						fLibFileList;
	public List<Integer>					fLibFileAttr;
	
	// List of all source files (roots + included)
	public List<String>						fSrcFileList;
	public List<Integer>					fSrcFileAttr;

	// Map from root file to included files
	public Map<String, List<String>>		fRootIncludeMap;
	
	public boolean							fMFCU;
	
	public boolean							fForceSV;
	
	public SVDBArgFileIndexCacheData(String base_location) {
		super(base_location);
		fArgFileTimestamps = new ArrayList<Long>();
		fArgFilePaths = new ArrayList<String>();
		fArgFiles = new ArrayList<SVDBFile>();
		fArgFileAttr = new ArrayList<Integer>();
		fLibFileList = new ArrayList<String>();
		fLibFileAttr = new ArrayList<Integer>();
		fSrcFileList = new ArrayList<String>();
		fSrcFileAttr = new ArrayList<Integer>();
		fRootIncludeMap = new HashMap<String, List<String>>();
	}

	public boolean containsFile(String path, int attr) {
		if ((attr & ISVDBDeclCache.FILE_ATTR_SRC_FILE) != 0) {
			if (fSrcFileList != null && fSrcFileList.contains(path)) {
				return true;
			}
		}
		
		if ((attr & ISVDBDeclCache.FILE_ATTR_ARG_FILE) != 0) {
			if (fArgFilePaths != null && fArgFilePaths.contains(path)) {
				return true;
			}
		}
		if ((attr & ISVDBDeclCache.FILE_ATTR_LIB_FILE) != 0) {
			if (fLibFileList != null && fLibFileList.contains(path)) {
				return true;
			}
		}
		
		return false;
	}
	
	public void addFile(String path, int flags) {
		
		if ((flags & ISVDBDeclCache.FILE_ATTR_SRC_FILE) != 0) {
			if ((flags & ISVDBDeclCache.FILE_ATTR_ROOT_FILE) != 0) {
				if (!fRootFileCacheData.containsKey(path)) {
					fRootFileCacheData.put(path, new SVDBRootFileCacheData());
				}
			} else if ((flags & ISVDBDeclCache.FILE_ATTR_LIB_FILE) != 0) {
				if (!fLibFileList.contains(path)) {
					fLibFileList.add(path);
					fLibFileAttr.add(flags);
				}
			}
			
			// All files are source files
			if (!fSrcFileList.contains(path)) {
				fSrcFileList.add(path);
				fSrcFileAttr.add(flags);
			}
		} else if ((flags & ISVDBDeclCache.FILE_ATTR_ARG_FILE) != 0) {
			if (!fArgFilePaths.contains(path)) {
				fArgFilePaths.add(path);
				fArgFileAttr.add(flags);
			}
		}
	}
	
	public int getFileAttr(String path) {
		int ret = 0;
		int idx;
		
		if ((idx = fSrcFileList.indexOf(path)) != -1) {
			ret = fSrcFileAttr.get(idx);
		} else if ((idx = fLibFileList.indexOf(path)) != -1) {
			ret = fLibFileAttr.get(idx);
		} else if ((idx = fArgFilePaths.indexOf(path)) != -1) {
			ret = fArgFileAttr.get(idx);
		}
			
		return ret;
	}
	
	public void setFileAttr(String path, int flags) {
		int idx;
		
		if ((idx = fSrcFileList.indexOf(path)) != -1) {
			fSrcFileAttr.set(idx, flags);
		} else if ((idx = fLibFileList.indexOf(path)) != -1) {
			fLibFileAttr.set(idx, flags);
		} else if ((idx = fArgFilePaths.indexOf(path)) != -1) {
			fArgFileAttr.set(idx, flags);
		}
	}
	
	public void setFileAttrBits(String path, int flags) {
		int idx, attr;
		
		if ((idx = fSrcFileList.indexOf(path)) != -1) {
			attr = fSrcFileAttr.get(idx);
			attr |= flags;
			fSrcFileAttr.set(idx, attr);
		} else if ((idx = fArgFilePaths.indexOf(path)) != -1) {
			attr = fArgFileAttr.get(idx);
			attr |= flags;
			fArgFileAttr.set(idx, attr);
		}
	}
	
	public void clrFileAttrBits(String path, int flags) {
		int idx, attr;
		
		if ((idx = fSrcFileList.indexOf(path)) != -1) {
			attr = fSrcFileAttr.get(idx);
			attr &= (~flags);
			fSrcFileAttr.set(idx, attr);
		} else if ((idx = fArgFilePaths.indexOf(path)) != -1) {
			attr = fArgFileAttr.get(idx);
			attr &= (~flags);
			fArgFileAttr.set(idx, attr);
		}
	}
	
	public List<String> getFileList(int flags) {
		List<String> ret = new ArrayList<String>();
		
		if ((flags & ISVDBDeclCache.FILE_ATTR_SRC_FILE) != 0) {
			if ((flags & ISVDBDeclCache.FILE_ATTR_ROOT_FILE) != 0) {
				for (String path : fRootFileCacheData.keySet()) {
					ret.add(path);
				}
			} else if ((flags & ISVDBDeclCache.FILE_ATTR_LIB_FILE) != 0) {
				for (String path : fLibFileList) {
					ret.add(path);
				}
			} else {
				for (String path : fSrcFileList) {
					ret.add(path);
				}
			}
		}
	
		if ((flags & ISVDBDeclCache.FILE_ATTR_ARG_FILE) != 0) {
			for (String path : fArgFilePaths) {
				ret.add(path);
			}
		}
		
		return ret;
	}
	
	public int getFileCount(int flags) {
		int ret = 0;
		if ((flags & ISVDBDeclCache.FILE_ATTR_SRC_FILE) != 0) {
			if ((flags & ISVDBDeclCache.FILE_ATTR_ROOT_FILE) != 0) {
				ret += fRootFileCacheData.size();
			} else {
				ret += fSrcFileList.size();
			}
		}
	
		if ((flags & ISVDBDeclCache.FILE_ATTR_ARG_FILE) != 0) {
			ret += fArgFilePaths.size();
		}
		
		return ret;
	}	
}
