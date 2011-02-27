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


package net.sf.sveditor.core.db.expr;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVExpr extends SVDBItemBase {
	
	private static Map<SVExprType, ISVExprPersistenceFactory>		fPersistenceFactoryMap;
	protected SVExprType			fExprType;
	
	static {
		fPersistenceFactoryMap = new HashMap<SVExprType, ISVExprPersistenceFactory>();
	}
	
	public static void init() {
		SVDBPersistenceReader.registerEnumType(SVExprType.class, SVExprType.values());
		
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				SVExprType expr_type = (SVExprType)reader.readEnumType(SVExprType.class);
				
				return readExpr(expr_type, reader);
			}
		};
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Expr);
		SVExprString.init();
	}
	
	public static void registerPersistenceFactory(
			ISVExprPersistenceFactory f, SVExprType ... types) {
		for (SVExprType t : types) {
			fPersistenceFactoryMap.put(t, f);
		}
	}
	
	private static SVExpr readExpr(SVExprType expr_type, IDBReader reader) throws DBFormatException {
		ISVExprPersistenceFactory f = fPersistenceFactoryMap.get(expr_type);
		
		if (f == null) {
			throw new DBFormatException("No persistence factory registered for SVExpr " + expr_type);
		}
		
		return f.readSVExpr(expr_type, reader);
	}

	public static SVExpr readExpr(IDBReader reader) throws DBFormatException {
		SVDBItemType type = reader.readItemType();
		
		if (type == SVDBItemType.NULL) {
			return null;
		}
		
		if (type != SVDBItemType.Expr) {
			throw new DBFormatException("Expecting type Expression, received " + type);
		}
		SVExprType expr_type = (SVExprType)reader.readEnumType(SVExprType.class);
		
		return readExpr(expr_type, reader);
	}
	
	public static void writeExpr(SVExpr expr, IDBWriter writer) {
		if (expr == null) {
			writer.writeItemType(SVDBItemType.NULL);
		} else {
			expr.dump(writer);
		}
	}

	public SVExpr(SVExprType type) {
		super(SVDBItemType.Expr);
		fExprType = type;
	}
	
	public SVExprType getExprType() {
		return fExprType;
	}
	
	public String toString() {
		return SVExprUtils.getDefault().exprToString(this);
	}
	
	public SVExpr duplicate() {
		SVExpr ret = new SVExpr(fExprType);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		SVExpr o = (SVExpr)other;
		fExprType = o.fExprType;
		super.init(o);
	}
}
