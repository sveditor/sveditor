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

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;

public class SVDBIndexSearcher implements ISVDBIndexSearcher {
	protected boolean								fDebugEn;
	protected List<SVDBIndexCollection>			fIndexCollection;
	
	public SVDBIndexSearcher() {
		fIndexCollection = new ArrayList<SVDBIndexCollection>();
	}
	
	public void addIndexCollection(SVDBIndexCollection mgr) {
		fIndexCollection.add(mgr);
	}
	
	public List<SVDBItem> findByName(String name, SVDBItemType... type_filter) {
		// TODO Auto-generated method stub
		return null;
	}

	public List<SVDBItem> findByNameInClassHierarchy(String name,
			SVDBScopeItem scope, SVDBItemType... type_filter) {
		// TODO Auto-generated method stub
		return null;
	}

	public List<SVDBItem> findByNameInScopes(String name, SVDBScopeItem scope,
			boolean stop_on_first_match, SVDBItemType... type_filter) {
		// TODO Auto-generated method stub
		return null;
	}

	public SVDBModIfcDecl findNamedModClassIfc(String name) {
		System.out.println("[FIXME] findNamedModClassIfc(" + name + ")");
		/*
		SVDBModIfcClassDecl c;
		for (SVDBFile f : fFiles) {
			if ((c= findNamedModClass(name, f)) != null) {
				return c;
			}
		}
		 */

		return null;
	}

	public SVDBModIfcDecl findSuperClass(SVDBModIfcDecl cls) {
		// TODO Auto-generated method stub
		return null;
	}

	public List<SVDBItem> findVarsByNameInScopes(String name,
			SVDBScopeItem scope, boolean stop_on_first_match) {
		// TODO Auto-generated method stub
		return null;
	}

	public void visitItems(ISVDBItemVisitor visitor, SVDBItemType type) {
		/*
		for (SVDBIndexCollectionMgr c : fIndexCollection) {
		}
		 */
	}

	public void visitItemsInTypeHierarchy(SVDBScopeItem scope,
			ISVDBItemVisitor visitor) {
		// TODO Auto-generated method stub

	}
	
	public SVDBFile findIncludedFile(String path) {
		/*
		for (SVDBIndexCollectionMgr c : fIndexCollection) {
			
		}
		 */
		return null;
	}

	protected void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}

}
