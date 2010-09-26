/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;

public class SVDBStructFieldFinder {
	private ISVDBFindNameMatcher				fMatcher;
	
	public SVDBStructFieldFinder(ISVDBFindNameMatcher matcher) {
		fMatcher = matcher;
	}
	
	public List<SVDBItem> find(SVDBTypeInfoStruct struct, String name) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		for (SVDBItem it : struct.getFields()) {
			if (fMatcher.match(it, name)) {
				ret.add(it);
			}
		}
		
		return ret;
	}

}
