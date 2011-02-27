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

public class SVDBPackageDecl extends SVDBScopeItem {
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBPackageDecl(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.PackageDecl); 
	}
	
	public SVDBPackageDecl(String name) {
		super(name, SVDBItemType.PackageDecl);
	}
	
	public SVDBPackageDecl(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
	}
	
	public SVDBItemBase duplicate() {
		SVDBPackageDecl ret = new SVDBPackageDecl(getName());
		
		ret.init(this);
		
		return ret;
	}
	
}
