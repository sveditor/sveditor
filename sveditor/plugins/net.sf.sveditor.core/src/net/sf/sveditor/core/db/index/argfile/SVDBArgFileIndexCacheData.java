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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;

public class SVDBArgFileIndexCacheData extends SVDBBaseIndexCacheData {
	
	public List<String>			fArgFilePaths;
	public List<Long>			fArgFileTimestamps;
	public List<SVDBFile>		fArgFiles = new ArrayList<SVDBFile>();
	
	// List of the root source files
	public List<String>			fRootFileList;
	
	// List of all source files (roots + included)
	public List<String>			fSrcFileList;

	// Map from root file to included files
	public Map<String, List<String>>		fRootIncludeMap;
	
	public boolean				fMFCU;
	
	public SVDBArgFileIndexCacheData(String base_location) {
		super(base_location);
		fArgFileTimestamps = new ArrayList<Long>();
		fArgFilePaths = new ArrayList<String>();
		fArgFiles = new ArrayList<SVDBFile>();
		fRootFileList = new ArrayList<String>();
		fSrcFileList = new ArrayList<String>();
		fRootIncludeMap = new HashMap<String, List<String>>();
	}

	/*
	public List<Long> getArgFileTimestamps() {
		return fArgFileTimestamps;
	}
	
	public List<String> getArgFilePaths() {
		return fArgFilePaths;
	}
	
	public List<SVDBFile> getArgFiles() {
		if (fArgFiles == null) {
			fArgFiles = new ArrayList<SVDBFile>();
		}
		return fArgFiles;
	}
	 */
	
}
