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
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBTypedefStmt extends SVDBStmt implements ISVDBNamedItem {
	private SVDBTypeInfo					fTypeInfo;
	// TODO: Add Vectored info
	
	private String							fName;
	
	public static void init() {
		SVDBPersistenceReader.registerPersistenceFactory(new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type,
					IDBReader reader) throws DBFormatException {
				return new SVDBTypedefStmt(parent, type, reader);
			}
		}, SVDBItemType.TypedefStmt);
	}

	public SVDBTypedefStmt(SVDBTypeInfo type) {
		super(SVDBItemType.TypedefStmt);
		fTypeInfo = type;
	}
	
	public SVDBTypedefStmt(SVDBTypeInfo type, String name) {
		this(type);
		fName = name;
	}
	
	public SVDBTypedefStmt(ISVDBItemBase parent, SVDBItemType stmt_type, IDBReader reader) throws DBFormatException {
		super(parent, stmt_type, reader);

		fTypeInfo = (SVDBTypeInfo)reader.readSVDBItem(this);
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
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
	public SVDBTypedefStmt duplicate() {
		SVDBTypedefStmt ret = new SVDBTypedefStmt(fTypeInfo.duplicate());
		
		ret.init(this);

		return ret;
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
		
		SVDBTypedefStmt ot = (SVDBTypedefStmt)other;
		fTypeInfo = ot.fTypeInfo.duplicate();
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypedefStmt) {
			SVDBTypedefStmt o = (SVDBTypedefStmt)obj;
			
			if (!o.fTypeInfo.equals(fTypeInfo)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}
	
}
