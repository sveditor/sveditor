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
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBCoverpointCross extends SVDBModIfcClassDecl {
	private List<String>		fCoverpointList;
	private String				fBody;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBCoverpointCross(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.CoverpointCross); 
	}
	

	public SVDBCoverpointCross(String name, String body) {
		super(name, SVDBItemType.CoverpointCross);
		fBody = body;
		fCoverpointList = new ArrayList<String>();
	}

	public List<String> getCoverpointList() {
		return fCoverpointList;
	}
	
	public SVDBCoverpointCross(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) 
		throws DBFormatException {
		super(file, parent, type, reader);

		fBody = reader.readString();
		fCoverpointList = reader.readStringList();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);

		writer.writeString(fBody);
		writer.writeStringList(fCoverpointList);
	}

	@Override
	public SVDBItem duplicate() {
		SVDBCoverpointCross ret = new SVDBCoverpointCross(getName(), fBody);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		SVDBCoverpointCross other_i = (SVDBCoverpointCross)other;
		
		super.init(other);
		
		fCoverpointList.clear();
		fCoverpointList.addAll(other_i.fCoverpointList);
	}

}
