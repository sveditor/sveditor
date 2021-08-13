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


package org.sveditor.core.db.index.plugin;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexFactory;
import org.sveditor.core.db.index.SVDBIndexConfig;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;

public class SVDBPluginLibIndexFactory implements ISVDBIndexFactory {
	
	public static final String			TYPE = "org.sveditor.pluginLibIndex"; 

	public ISVDBIndex createSVDBIndex(
			String 					project, 
			String 					base_location,
			ISVDBIndexCache			cache,
			SVDBIndexConfig			config) {
		for (SVDBPluginLibDescriptor d : SVCorePlugin.getDefault().getPluginLibList()) {
			if (d.getId().equals(base_location)) {
				return new SVDBPluginLibIndex(
						project, 
						d.getId(), 
						d.getNamespace(), 
						d.getPath(), 
						cache);
			}
		}
		
		return null;
	}

}
