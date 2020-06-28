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


package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;

public class SVDBFindAllMatcher implements ISVDBFindNameMatcher {
	
	static SVDBFindAllMatcher 		fDefault;

	public boolean match(ISVDBNamedItem it, String name) {
		return true;
	}
	
	public static SVDBFindAllMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindAllMatcher();
		}
		return fDefault;
	}
	
}
