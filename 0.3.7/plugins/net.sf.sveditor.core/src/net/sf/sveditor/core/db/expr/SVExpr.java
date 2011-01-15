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

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVExpr extends SVDBItemBase {
	
	protected SVExprType			fExprType;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type,
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				// TODO Auto-generated method stub
				return null;
			}
		};
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Expr);
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
	
	public SVDBItemBase duplicate() {
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
