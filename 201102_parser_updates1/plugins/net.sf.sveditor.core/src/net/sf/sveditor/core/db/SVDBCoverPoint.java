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

public class SVDBCoverPoint extends SVDBScopeItem {
	private SVExpr				fTarget;
	private SVExpr				fIFF;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBCoverPoint(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Coverpoint); 
	}
	
	
	public SVDBCoverPoint(String name) {
		super(name, SVDBItemType.Coverpoint);
	}
	
	public SVExpr getTarget() {
		return fTarget;
	}
	
	public void setTarget(SVExpr expr) {
		fTarget = expr;
	}
	
	public SVExpr getIFF() {
		return fIFF;
	}
	
	public void setIFF(SVExpr expr) {
		fIFF = expr;
	}
	
	public SVDBCoverPoint(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) 
		throws DBFormatException {
		super(parent, type, reader);
		
		fTarget = SVExpr.readExpr(reader);
		fIFF = SVExpr.readExpr(reader); 
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		SVExpr.writeExpr(fTarget, writer);
		SVExpr.writeExpr(fIFF, writer);
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBCoverPoint ret = new SVDBCoverPoint(getName());
		
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
			// TODO:
			return true;
		} else {
			return false;
		}
	}
	
}
