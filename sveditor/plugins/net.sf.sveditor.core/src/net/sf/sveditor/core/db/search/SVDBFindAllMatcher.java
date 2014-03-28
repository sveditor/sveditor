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
