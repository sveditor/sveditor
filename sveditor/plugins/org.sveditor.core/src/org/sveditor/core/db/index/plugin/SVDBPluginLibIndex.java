/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.db.index.plugin;

import org.eclipse.core.runtime.Platform;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.sveditor.core.log.LogFactory;

public class SVDBPluginLibIndex extends SVDBArgFileIndex {
	
	public SVDBPluginLibIndex(
			String 			project, 
			String			index_id,
			String			plugin_ns,
			String			root,
			ISVDBIndexCache	cache) {
		super(project, 
				"plugin:/" + plugin_ns + "/" + root,
				new SVDBPluginFileSystemProvider(
						Platform.getBundle(plugin_ns), plugin_ns),
				cache,
				null);
		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");
	}
	
}
