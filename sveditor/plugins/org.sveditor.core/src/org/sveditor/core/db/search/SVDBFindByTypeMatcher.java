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

public class SVDBFindByTypeMatcher implements ISVDBFindNameMatcher {
	private SVDBItemType			fTypes[];
	
	public SVDBFindByTypeMatcher(SVDBItemType ... types) {
		fTypes = types;
	}

	@Override
	public boolean match(ISVDBNamedItem it, String name) {
		return (fTypes == null || fTypes.length == 0 ||
				it.getType().isElemOf(fTypes));
	}
}
