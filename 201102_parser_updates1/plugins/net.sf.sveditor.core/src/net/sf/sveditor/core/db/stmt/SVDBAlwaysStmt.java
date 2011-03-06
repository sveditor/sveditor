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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBAlwaysStmt extends SVDBBodyStmt {
	
	public enum AlwaysType {
		Always,
		AlwaysComb,
		AlwaysLatch,
		AlwaysFF
	};
	
	private AlwaysType		fAlwaysType;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBAlwaysStmt(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.AlwaysStmt);
		SVDBPersistenceReader.registerEnumType(AlwaysType.class, AlwaysType.values());
	}
	
	public SVDBAlwaysStmt(AlwaysType type) {
		super(SVDBItemType.AlwaysStmt);
		fAlwaysType = type;
	}
	
	public SVDBAlwaysStmt(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fAlwaysType = (AlwaysType)reader.readEnumType(AlwaysType.class);
	}
	
	public AlwaysType getAlwaysType() {
		return fAlwaysType;
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeEnumType(AlwaysType.class, fAlwaysType);
	}

	@Override
	public SVDBAlwaysStmt duplicate() {
		SVDBAlwaysStmt ret = new SVDBAlwaysStmt(fAlwaysType);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
		fAlwaysType = ((SVDBAlwaysStmt)other).fAlwaysType;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBAlwaysStmt) {
			boolean ret = true;
			ret &= ((SVDBAlwaysStmt)obj).fAlwaysType.equals(fAlwaysType);
			ret &= super.equals(obj);
			
			return ret;
		}
		return false;
	}
	
}
