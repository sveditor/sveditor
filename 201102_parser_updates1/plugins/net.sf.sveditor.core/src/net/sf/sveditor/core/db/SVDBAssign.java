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
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBAssign extends SVDBStmt {
	
	private SVExpr				fLHS;
	private SVExpr				fDelay;
	private SVExpr				fRHS;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBAssign(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Assign); 
	}
	
	public SVDBAssign() {
		super(SVDBItemType.Assign);
	}
	
	public SVDBAssign(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
	}
	
	public void setLHS(SVExpr lhs) {
		fLHS = lhs;
	}
	
	public SVExpr getLHS() {
		return fLHS;
	}
	
	public void setDelay(SVExpr delay) {
		fDelay = delay;
	}
	
	public SVExpr getDelay() {
		return fDelay;
	}
	
	public void setRHS(SVExpr rhs) {
		fRHS = rhs;
	}
	
	public SVExpr getRHS() {
		return fRHS;
	}
	
	public SVDBAssign duplicate() {
		SVDBAssign ret = new SVDBAssign();
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
	}

}
