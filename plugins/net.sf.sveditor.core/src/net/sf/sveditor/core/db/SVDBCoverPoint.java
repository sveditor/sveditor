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

public class SVDBCoverPoint extends SVDBModIfcClassDecl {
	private String				fTarget;
	private String				fBody;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBCoverPoint(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Coverpoint); 
	}
	
	
	public SVDBCoverPoint(String name, String target, String body) {
		super(name, SVDBItemType.Coverpoint);
		fTarget = target;
		fBody = body;
	}
	
	public String getTarget() {
		return fTarget;
	}
	
	public String getBody() {
		return fBody;
	}
	
	public SVDBCoverPoint(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) 
		throws DBFormatException {
		super(file, parent, type, reader);
		
		fTarget = reader.readString();
		fBody = reader.readString();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fTarget);
		writer.writeString(fBody);
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBCoverPoint ret = new SVDBCoverPoint(getName(), fTarget, fBody);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		SVDBCoverPoint other_i = (SVDBCoverPoint)other;
		
		super.init(other);
		
		fTarget = other_i.fTarget;
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBCoverPoint) {
			return ((SVDBCoverPoint)obj).fTarget.equals(fTarget) &&
				((SVDBCoverPoint)obj).fBody.equals(fBody) &&
				super.equals(obj);
		} else {
			return false;
		}
	}
	
}
