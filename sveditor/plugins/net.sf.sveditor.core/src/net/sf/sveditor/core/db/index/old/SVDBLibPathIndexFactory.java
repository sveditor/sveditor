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


package net.sf.sveditor.core.db.index.old;

import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

public class SVDBLibPathIndexFactory implements ISVDBIndexFactory {
	
	public static final String			TYPE = "net.sf.sveditor.libIndex";

	public ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			ISVDBIndexCache			cache,
			SVDBIndexConfig			config) {
		ISVDBFileSystemProvider fs_provider;
		
		fs_provider = new SVDBWSFileSystemProvider();
		/*
		if (base_location.startsWith("${workspace_loc}")) {
		} else {
			fs_provider = new SVDBFSFileSystemProvider();
		}
		 */
		
		ISVDBIndex index = new SVDBLibIndex(
				project_name, base_location, fs_provider, cache, config);
		
		return index;
	}

}
