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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBTypeInfoStruct extends SVDBTypeInfo implements ISVDBScopeItem {
	public long								fEndLocation;
	public List<SVDBVarDeclStmt>			fFields;
	
	public SVDBTypeInfoStruct() {
		super("<<ANONYMOUS>>", SVDBItemType.TypeInfoStruct);
		fFields = new ArrayList<SVDBVarDeclStmt>();
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
	
	@SuppressWarnings({"rawtypes","unchecked"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fFields.iterator();
			}
		};
	}

	public void addItem(ISVDBItemBase item) {
	}

	public List<SVDBVarDeclStmt> getFields() {
		return fFields;
	}
	
	public void addChildItem(ISVDBChildItem f) {
		fFields.add((SVDBVarDeclStmt)f);
		f.setParent(this);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoStruct) {
			SVDBTypeInfoStruct o = (SVDBTypeInfoStruct)obj;
			
			if (fFields.size() == o.fFields.size()) {
				for (int i=0; i<fFields.size(); i++) {
					if (!fFields.get(i).equals(o.fFields.get(i))) {
						return false;
					}
				}
			} else {
				return false;
			}
			return super.equals(obj);
		}
		return false;
	}

	@Override
	public SVDBTypeInfoStruct duplicate() {
		return (SVDBTypeInfoStruct)super.duplicate();
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_type_info_struct(this);
	}
}
