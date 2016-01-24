/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index.argfile;

import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

public class SVDBArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.argFileIndex";
	
	public ISVDBIndex createSVDBIndex(
			String 					projectName, 
			String 					base_location,
			ISVDBIndexCache			cache,
			SVDBIndexConfig 		config) {
		ISVDBFileSystemProvider fs_provider;
		
		fs_provider = new SVDBWSFileSystemProvider();
		
		ISVDBIndex ret = new SVDBArgFileIndex(
				projectName, base_location, fs_provider, cache, config);
		
		return ret;
	}

}

