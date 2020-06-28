/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBTypeInfoUnion extends SVDBTypeInfo implements ISVDBScopeItem {
	public long								fEndLocation;
	public List<SVDBVarDeclStmt>			fFields;
	
	public SVDBTypeInfoUnion() {
		super("<<ANONYMOUS>>", SVDBItemType.TypeInfoUnion);
		fFields = new ArrayList<SVDBVarDeclStmt>();
	}

	@SuppressWarnings({"rawtypes","unchecked"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fFields.iterator();
			}
		};
	}

	public void addChildItem(ISVDBChildItem f) {
		fFields.add((SVDBVarDeclStmt)f);
		f.setParent(this);
	}

	public long getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(long loc) {
		fEndLocation = loc;
	}

	// Deprecated methods
	@SuppressWarnings({"rawtypes","unchecked"})
	public List<ISVDBItemBase> getItems() {
		return (List)fFields;
	}

	public void addItem(ISVDBItemBase item) {
	}

}
