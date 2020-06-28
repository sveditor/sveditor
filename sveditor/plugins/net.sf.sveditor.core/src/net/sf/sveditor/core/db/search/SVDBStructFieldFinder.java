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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;

public class SVDBStructFieldFinder {
	private ISVDBFindNameMatcher				fMatcher;
	
	public SVDBStructFieldFinder(ISVDBFindNameMatcher matcher) {
		fMatcher = matcher;
	}
	
	public List<ISVDBItemBase> find(SVDBTypeInfoStruct struct, String name) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		for (ISVDBItemBase it : struct.getFields()) {
			if (it instanceof ISVDBNamedItem) {
				if (fMatcher.match((ISVDBNamedItem)it, name)) {
					ret.add(it);
				}
			}
		}
		
		return ret;
	}

}
