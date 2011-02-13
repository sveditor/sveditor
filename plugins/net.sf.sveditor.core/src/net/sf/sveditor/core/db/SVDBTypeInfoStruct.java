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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBTypeInfoStruct extends SVDBTypeInfo {
	private List<SVDBVarDeclStmt>			fFields;
	
	public SVDBTypeInfoStruct() {
		super("<<ANONYMOUS>>", SVDBDataType.Struct);
		fFields = new ArrayList<SVDBVarDeclStmt>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBTypeInfoStruct(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.Struct, file, parent, type, reader);
		fFields = (List<SVDBVarDeclStmt>)reader.readItemList(file, parent);
	}
	
	public List<SVDBVarDeclStmt> getFields() {
		return fFields;
	}
	
	public void addField(SVDBVarDeclStmt f) {
		fFields.add(f);
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeItemList(fFields);
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
		SVDBTypeInfoStruct ret = new SVDBTypeInfoStruct();
		ret.setName(getName());
		
		for (SVDBVarDeclStmt f : fFields) {
			ret.addField((SVDBVarDeclStmt)f.duplicate());
		}
		
		return ret;
	}
}
