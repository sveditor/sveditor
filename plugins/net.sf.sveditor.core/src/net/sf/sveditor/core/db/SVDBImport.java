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
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBImport extends SVDBItem {
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBImport(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Import); 
	}
	
	public SVDBImport(String imp) {
		super(imp, SVDBItemType.Import);
	}
	
	public SVDBImport(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBImport ret = new SVDBImport(getName());
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
	}

	@Override
	public boolean equals(Object obj) {
		return super.equals(obj);
	}
	
}
