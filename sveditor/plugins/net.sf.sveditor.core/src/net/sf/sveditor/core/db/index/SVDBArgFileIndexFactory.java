/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

public class SVDBArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.argFileIndex";
	
	public static boolean		fUseArgFile2Index = false;

	public ISVDBIndex createSVDBIndex(
			String 					projectName, 
			String 					base_location,
			ISVDBIndexCache			cache,
			SVDBIndexConfig 		config) {
		ISVDBFileSystemProvider fs_provider;
		
		fs_provider = new SVDBWSFileSystemProvider();
		
		ISVDBIndex ret = null;

		if (fUseArgFile2Index) {
			ret = new SVDBArgFileIndex2(
				projectName, base_location, fs_provider, cache, config);
		} else {
			ret = new SVDBArgFileIndex(
				projectName, base_location, fs_provider, cache, config);
		}
		
		return ret;
	}

	/*
	public ISVDBIndex createSVDBIndex(
			String 					projectName, 
			String 					base_location,
			StringBuilder			arguments,
			ISVDBIndexCache			cache,
			SVDBIndexConfig		 	config) {
		ISVDBFileSystemProvider fs_provider;
		
		fs_provider = new SVDBWSFileSystemProvider();
//		if (base_location.startsWith("${workspace_loc}")) {
//		} else {
//			fs_provider = new SVDBFSFileSystemProvider();
//		}

		SVDBArgFileIndex index = new SVDBArgFileIndex(
				projectName, base_location, arguments, fs_provider, cache, config);
		
		return index;
	}
	 */


}
