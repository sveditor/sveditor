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

import java.util.List;

import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.stmt.SVDBParamPort;

public class SVDBCoverGroup extends SVDBModIfcClassDecl {
	public enum BinsKW {
		Bins,
		IllegalBins,
		IgnoreBins
	};
	
	private SVExpr				fCoverageEventExpr;
	private List<SVDBParamPort>	fParamPort;

	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBCoverGroup(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Covergroup); 
	}
	
	public SVDBCoverGroup(String name) {
		super(name, SVDBItemType.Covergroup);
	}
	
	public SVDBCoverGroup(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
	}
	
	public void setParamPort(List<SVDBParamPort> params) {
		fParamPort = params;
	}
	
	public List<SVDBParamPort> getParamPort() {
		return fParamPort;
	}
	
	public void setCoverageEvent(SVExpr expr) {
		fCoverageEventExpr = expr;
	}
	
	public SVExpr getCoverageEvent() {
		return fCoverageEventExpr;
	}
	
	public SVDBCoverGroup duplicate() {
		SVDBCoverGroup cg = new SVDBCoverGroup(getName());
		
		cg.init(this);
		
		return cg;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
	}
	
}
