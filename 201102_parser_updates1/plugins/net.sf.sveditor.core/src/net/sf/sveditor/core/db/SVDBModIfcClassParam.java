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

import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBModIfcClassParam extends SVDBItem {
	
	private SVExpr					fDefault;

	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBModIfcClassParam(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.ModIfcClassParam); 
	}

	public SVDBModIfcClassParam(String name) {
		super(name, SVDBItemType.ModIfcClassParam);
	}
	
	public SVDBModIfcClassParam(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		
		fDefault = SVExpr.readExpr(reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		SVExpr.writeExpr(fDefault, writer);
	}
	
	public SVExpr getDefault() {
		return fDefault;
	}
	
	public void setDefault(SVExpr dflt) {
		fDefault = dflt;
	}
	
	public SVDBItemBase duplicate() {
		SVDBItem ret = new SVDBModIfcClassParam(getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		fDefault = ((SVDBModIfcClassParam)other).fDefault;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBModIfcClassParam) {
			boolean ret = fDefault.equals(((SVDBModIfcClassParam)obj).fDefault);
			ret &= super.equals(obj);
			
			return ret;
		}
		
		return false;
	}
	
}
