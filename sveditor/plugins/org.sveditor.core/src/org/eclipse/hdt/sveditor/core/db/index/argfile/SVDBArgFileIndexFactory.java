/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.sveditor.core.db.index.argfile;

import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexFactory;
import org.sveditor.core.db.index.SVDBIndexConfig;
import org.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;

public class SVDBArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "org.sveditor.argFileIndex";
	
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

