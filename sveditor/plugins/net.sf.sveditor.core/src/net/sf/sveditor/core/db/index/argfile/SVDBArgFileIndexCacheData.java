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


package net.sf.sveditor.core.db.index.argfile;

import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;

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
	
//	public List<String>						fArgFilePaths;
//	public List<Integer>					fArgFileAttr;
//	public List<Long>						fArgFileTimestamps;
//	public List<SVDBFile>					fArgFiles = new ArrayList<SVDBFile>();
	
	// List of the library files
//	public List<String>						fLibFileList;
//	public List<Integer>					fLibFileAttr;
	
	// List of all source files (roots + included)
//	public List<String>						fSrcFileList;
//	public List<Integer>					fSrcFileAttr;

	// Map from root file to included files
//	public Map<String, List<String>>		fRootIncludeMap;
	
	
//	public boolean							fForceSV;
	
	public SVDBArgFileIndexCacheData(String base_location) {
		super(base_location);
//		fArgFileTimestamps = new ArrayList<Long>();
//		fArgFilePaths = new ArrayList<String>();
//		fArgFiles = new ArrayList<SVDBFile>();
//		fArgFileAttr = new ArrayList<Integer>();
//		fLibFileList = new ArrayList<String>();
//		fLibFileAttr = new ArrayList<Integer>();
//		fSrcFileList = new ArrayList<String>();
//		fSrcFileAttr = new ArrayList<Integer>();
//		fRootIncludeMap = new HashMap<String, List<String>>();
	}


	
	
}
