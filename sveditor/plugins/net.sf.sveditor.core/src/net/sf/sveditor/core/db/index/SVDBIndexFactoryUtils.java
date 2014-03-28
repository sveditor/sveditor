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


package net.sf.sveditor.core.db.index;

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
