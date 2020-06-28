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


package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;


public interface ISVDBIndexFactory {
	
	String KEY_GlobalDefineMap  = "svdb.index.factory.global_define_map";
	
	ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			ISVDBIndexCache			cache,
			SVDBIndexConfig			config);

}
