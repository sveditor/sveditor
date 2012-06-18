/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial contributor
 ****************************************************************************/

package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFindPackageDefaultNameMatcher implements ISVDBFindNameMatcher {

	static SVDBFindPackageDefaultNameMatcher 		fDefault;

	public boolean match(ISVDBNamedItem it, String name) {
		return (it.getType() == SVDBItemType.PackageDecl &&
				it.getName() != null && it.getName().equals(name));
	}
	
	public static SVDBFindPackageDefaultNameMatcher getDefault() {
		if (fDefault == null) {
			fDefault = new SVDBFindPackageDefaultNameMatcher();
		}
		return fDefault;
	}

}
