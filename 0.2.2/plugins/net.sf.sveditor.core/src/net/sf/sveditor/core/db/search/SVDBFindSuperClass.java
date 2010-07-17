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

import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBFindSuperClass {
	
	ISVDBIndexIterator				fIndexIterator;
	private ISVDBFindNameMatcher	fMatcher;


	public SVDBFindSuperClass(
			ISVDBIndexIterator 		index_it, 
			ISVDBFindNameMatcher	matcher) {
		fIndexIterator = index_it;
		fMatcher = matcher;
	}

	public SVDBFindSuperClass(ISVDBIndexIterator index_it) {
		this(index_it, SVDBFindDefaultNameMatcher.getDefault());
	}

	public SVDBModIfcClassDecl find(SVDBModIfcClassDecl cls) {
		if (cls.getSuperClass() != null) {
			SVDBFindNamedModIfcClassIfc finder = 
				new SVDBFindNamedModIfcClassIfc(fIndexIterator, fMatcher);
			
			List<SVDBModIfcClassDecl> ret = finder.find(cls.getSuperClass());
			
			return (ret.size() > 0)?ret.get(0):null;
		} else {
			return null;
		}
	}

}
