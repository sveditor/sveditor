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

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBTypeInfo extends SVDBItem {
	public static final int				TypeAttr_Vectored			= (1 << 6);

	protected SVDBDataType				fDataType;

	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type,
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				// First, read the sub-type
				SVDBDataType dt = SVDBDataType.valueOf(reader.readString());
				switch (dt) {
					case BuiltIn:
						return new SVDBTypeInfoBuiltin(file, parent, type, reader);
					case Enum:
						return new SVDBTypeInfoEnum(file, parent, type, reader);
					case Struct:
						return new SVDBTypeInfoStruct(file, parent, type, reader);
					case UserDefined:
					case ModuleIfc:
						return new SVDBTypeInfoUserDef(dt, file, parent, type, reader);
					case FwdDecl:
						return new SVDBTypeInfoFwdDecl(file, parent, type, reader);
					case WireBuiltin:
						return new SVDBTypeInfoBuiltinNet(file, parent, type, reader);
					default:
						throw new DBFormatException("[ERROR] Unhandled DataType " + dt);
				}
			}
		};
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.TypeInfo);
	}
	
	public SVDBTypeInfo(String typename, SVDBDataType data_type) {
		super(typename, SVDBItemType.TypeInfo);
		fDataType = data_type;
		fLocation = null;
	}

	public SVDBTypeInfo(SVDBDataType dt, SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super("", SVDBItemType.TypeInfo);
		
		fDataType = dt;
		setType(type);
		setName(reader.readString());
		fLocation = null;
	}
	
	public void dump(IDBWriter writer) {
		writer.writeItemType(getType());
		writer.writeString(fDataType.toString());
		writer.writeString(getName());
		// TypeInfo doesn't have a location: writer.writeInt((getLocation() != null)?getLocation().getLine():0);
	}
	
	public SVDBDataType getDataType() {
		return fDataType;
	}
	

	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBTypeInfo other_t = (SVDBTypeInfo)other;
		fDataType = other_t.fDataType;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfo) {
			SVDBTypeInfo o = (SVDBTypeInfo)obj;
			
			if (o.fDataType != fDataType) {
				return false;
			}

			return super.equals(obj);
		}
		return false;
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBTypeInfo ret = new SVDBTypeInfo(getName(), fDataType);
		ret.init(this);

		return ret;
	}
	
}
