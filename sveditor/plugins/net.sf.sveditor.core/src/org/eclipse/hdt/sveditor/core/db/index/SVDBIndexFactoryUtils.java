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


package org.eclipse.hdt.sveditor.core.db.index;

import java.util.Map;

public class SVDBIndexFactoryUtils {
	
	@SuppressWarnings("unchecked")
	public static void setBaseProperties(
			Map<String, Object>		config,
			ISVDBIndex				index) {
		if (config != null) {
			if (config.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
				Map<String, String> define_map = (Map<String, String>)
					config.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
				
				for (String key : define_map.keySet()) {
					index.setGlobalDefine(key, define_map.get(key));
				}
			}
		}
	}

}
