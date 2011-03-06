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
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBConstraint extends SVDBItem {
	private List<SVDBStmt>		fConstraintList;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBConstraint(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Constraint); 
	}
	
	
	public SVDBConstraint() {
		super("", SVDBItemType.Constraint);
		fConstraintList = new ArrayList<SVDBStmt>();
	}

	public List<SVDBStmt> getConstraintList() {
		return fConstraintList;
	}
	
	public void addConstraint(SVDBStmt stmt) {
		fConstraintList.add(stmt);
	}
	
	@SuppressWarnings("unchecked")
	public SVDBConstraint(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		
		fConstraintList = (List<SVDBStmt>)reader.readItemList(this);
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);

		writer.writeItemList(fConstraintList);
	}


	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBConstraint) {
			return ((SVDBConstraint)obj).fConstraintExpr.equals(fConstraintExpr) &&
				super.equals(obj);
		}
		return false;
	}
	 */
	
}
