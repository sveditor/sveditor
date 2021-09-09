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


package org.sveditor.core.db.search;

import java.util.List;

import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBTypeInfoClassType;
import org.sveditor.core.db.index.ISVDBIndexIterator;

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
		this(index_it, SVDBFindClassDefaultNameMatcher.getDefault());
	}

	public SVDBClassDecl find(SVDBClassDecl cls) {
		if (cls.getSuperClass() != null) {
			SVDBFindNamedClass finder = new SVDBFindNamedClass(fIndexIterator, fMatcher);
			SVDBTypeInfoClassType cls_type = cls.getSuperClass();
			
			List<SVDBClassDecl> ret = finder.findItem(cls_type.getName());
			
			return (ret.size() > 0)?ret.get(0):null;
		} else {
			return null;
		}
	}
	
}
