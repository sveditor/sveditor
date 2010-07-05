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


public class SVDBPreProcCond extends SVDBScopeItem {
	private String						fConditional;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBPreProcCond(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.PreProcCond); 
	}
	
	
	public SVDBPreProcCond(String name, String conditional) {
		super(name, SVDBItemType.PreProcCond);
		fConditional = conditional;
	}
	
	public SVDBPreProcCond(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fConditional = reader.readString();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fConditional);
	}
	
	
	public String getConditional() {
		return fConditional;
	}
	
	public SVDBItem duplicate() {
		SVDBPreProcCond ret = new SVDBPreProcCond(getName(), fConditional);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
	}
	
	public boolean equals(Object obj) {
		if (super.equals(obj) && obj instanceof SVDBPreProcCond) {
			return fConditional.equals(((SVDBPreProcCond)obj).fConditional) &&
				super.equals(obj);
		}
		return false;
	}
}
