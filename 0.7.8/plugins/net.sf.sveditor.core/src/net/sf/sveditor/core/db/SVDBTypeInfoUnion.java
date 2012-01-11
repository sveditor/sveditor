/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
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
	SVDBLocation					fEndLocation;
	List<SVDBVarDeclStmt>			fFields;
	
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

	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(SVDBLocation loc) {
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
