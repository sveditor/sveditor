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
