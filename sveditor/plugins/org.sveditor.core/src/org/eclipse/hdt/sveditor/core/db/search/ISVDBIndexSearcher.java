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

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;

public interface ISVDBIndexSearcher {
	
	SVDBModIfcDecl findNamedModClassIfc(String name);
	
	
	/** 
	 * Visits items of a particular type
	 * 
	 * @param visitor
	 * @param types
	 */
	void visitItems(
			ISVDBItemVisitor		visitor,
			SVDBItemType  			type);

	void visitItemsInTypeHierarchy(
			SVDBScopeItem			scope,
			ISVDBItemVisitor		visitor);

	List<SVDBItem> findByNameInScopes(
			String					name,
			SVDBScopeItem			scope,
			boolean					stop_on_first_match,
			SVDBItemType	...		type_filter);

	List<SVDBItem> findVarsByNameInScopes(
			String					name,
			SVDBScopeItem			scope,
			boolean					stop_on_first_match);

	List<SVDBItem> findByName(
			String					name,
			SVDBItemType	...		type_filter);
	
	List<SVDBItem> findByNameInClassHierarchy(
			String					name,
			SVDBScopeItem			scope,
			SVDBItemType	...		type_filter);
	
	SVDBModIfcDecl findSuperClass(SVDBModIfcDecl cls);
	
	SVDBFile findIncludedFile(String path);
		
}
