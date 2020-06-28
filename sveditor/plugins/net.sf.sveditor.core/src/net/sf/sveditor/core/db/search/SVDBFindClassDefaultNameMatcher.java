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
package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFindClassDefaultNameMatcher implements ISVDBFindNameMatcher {

	static SVDBFindClassDefaultNameMatcher 		fDefault;

	public boolean match(ISVDBNamedItem it, String name) {
		return (it.getType() == SVDBItemType.ClassDecl &&
				it.getName() != null && it.getName().equals(name));
	}
	
	public static SVDBFindClassDefaultNameMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindClassDefaultNameMatcher();
		}
		return fDefault;
	}

}
