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
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type,
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				// First, read the sub-type
				return new SVDBTypeInfo(file, parent, type, reader);
			}
		};
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.TypeInfo);
	}
	
	public SVDBTypeInfo(String typename, SVDBDataType data_type) {
		super(typename, SVDBItemType.TypeInfo);
		fDataType = data_type;
	}

	public SVDBTypeInfo(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		
		fDataType = SVDBDataType.valueOf(reader.readString());
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);

		writer.writeString(fDataType.toString());
	}
	
	public SVDBDataType getDataType() {
		return fDataType;
	}
	

	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBTypeInfo other_t = (SVDBTypeInfo)other;
		fDataType = other_t.fDataType;
	}
	
}
