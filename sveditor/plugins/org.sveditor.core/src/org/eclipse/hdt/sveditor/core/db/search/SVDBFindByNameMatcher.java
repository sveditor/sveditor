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
package org.sveditor.core.db.search;

import org.sveditor.core.db.ISVDBNamedItem;
import org.sveditor.core.db.SVDBItemType;

public class SVDBFindByNameMatcher implements ISVDBFindNameMatcher {
	private SVDBItemType						fTypes[];
	private static SVDBFindByNameMatcher		fDefault = null;
	
	public SVDBFindByNameMatcher(SVDBItemType ... types) {
		fTypes = types;
	}

	public boolean match(ISVDBNamedItem it, String name) {
		if (fTypes.length == 0) {
			return (it.getName().equals(name));
		} else {
			return (it.getType().isElemOf(fTypes) && it.getName().equals(name));
		}
	}
	
	public static SVDBFindByNameMatcher getDefault() { 
		if (fDefault == null) {
			fDefault = new SVDBFindByNameMatcher();
		}
		return fDefault;
	}

}
