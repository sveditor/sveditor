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

public class SVDBConstraint extends SVDBItem {
	private String				fConstraintExpr;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBConstraint(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Constraint); 
	}
	
	
	public SVDBConstraint(String name) {
		super(name, SVDBItemType.Constraint);
		fConstraintExpr = "";
	}

	public SVDBConstraint(String name, String expr) {
		super(name, SVDBItemType.Constraint);
		fConstraintExpr = expr;
	}

	public String getConstraintExpr() {
		return fConstraintExpr;
	}
	
	public void setConstraintExpr(String expr) {
		fConstraintExpr = expr;
	}
	
	public SVDBConstraint(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		
		fConstraintExpr = reader.readString();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fConstraintExpr);
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBConstraint) {
			return ((SVDBConstraint)obj).fConstraintExpr.equals(fConstraintExpr) &&
				super.equals(obj);
		}
		return false;
	}
	
}
