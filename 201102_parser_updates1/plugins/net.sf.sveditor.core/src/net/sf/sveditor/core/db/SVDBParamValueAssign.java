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

public class SVDBParamValueAssign extends SVDBItem {
	private SVExpr					fValue;
	private SVDBTypeInfo			fType;

	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBParamValueAssign(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(
				f, SVDBItemType.ParamValue); 
	}

	public SVDBParamValueAssign(String name, SVExpr value) {
		super(name, SVDBItemType.ParamValue);
		fValue = value;
	}

	public SVDBParamValueAssign(String name, SVDBTypeInfo type) {
		super(name, SVDBItemType.ParamValue);
		fType = type;
	}

	public SVDBParamValueAssign(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fValue = SVExpr.readExpr(reader);
	}
	

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		SVExpr.writeExpr(fValue, writer);
	}
	
	public SVExpr getValue() {
		return fValue;
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBParamValueAssign ret = new SVDBParamValueAssign(getName(), fValue);
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		
		fValue = ((SVDBParamValueAssign)other).fValue;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBParamValueAssign) {
			return (fValue.equals(((SVDBParamValueAssign)obj).fValue) &&
					super.equals(obj));
		}
		
		return false;
	}
	
}
