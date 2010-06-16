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

public class SVDBTypedef extends SVDBItem {
	private SVDBTypeInfo					fTypeInfo;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBTypedef(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Typedef); 
	}
	
	
	public SVDBTypedef(SVDBTypeInfo type, String name) {
		super(name, SVDBItemType.Typedef);
		fTypeInfo = type;
	}
	
	public SVDBTypedef(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);

		fTypeInfo = (SVDBTypeInfo)reader.readSVDBItem(file, parent);
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);

		writer.writeSVDBItem(fTypeInfo);
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}
	
	@Override
	public SVDBItem duplicate() {
		SVDBTypedef ret = new SVDBTypedef(
				(SVDBTypeInfo)fTypeInfo.duplicate(), getName());
		
		ret.init(this);

		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBTypedef ot = (SVDBTypedef)other;
		fTypeInfo = ot.fTypeInfo;
	}
	
}
