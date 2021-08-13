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


package org.eclipse.hdt.sveditor.core.db.search;

import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;

public class SVDBFindDefaultNameMatcher implements ISVDBFindNameMatcher {
	
	static SVDBFindDefaultNameMatcher 		fDefault;

	public boolean match(ISVDBNamedItem it, String name) {
		return (it.getName() != null && it.getName().equals(name));
	}
	
	public static SVDBFindDefaultNameMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindDefaultNameMatcher();
		}
		return fDefault;
	}
	
}
