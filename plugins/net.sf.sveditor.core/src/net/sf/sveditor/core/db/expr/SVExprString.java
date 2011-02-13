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

import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

/**
 * Temporary class that represents an expression as a string. This 
 * class will be obsolete when the implementation of full expression parsing 
 * is complete 
 * 
 * @author ballance
 *
 */
public class SVExprString extends SVExpr {
	private String				fExprStr;
	
	public static void init() {
		SVExpr.registerPersistenceFactory(new ISVExprPersistenceFactory() {
			
			public SVExpr readSVExpr(SVExprType type, IDBReader reader)
					throws DBFormatException {
				return new SVExprString(type, reader);
			}
		}, SVExprType.ExprString);
	}
	
	public SVExprString(String expr) {
		super(SVExprType.ExprString);
		fExprStr = expr;
	}
	
	public SVExprString(SVExprType type, IDBReader reader) throws DBFormatException {
		super(SVExprType.ExprString);
		fExprStr = reader.readString();
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fExprStr);
	}

	@Override
	public String toString() {
		return fExprStr;
	}

	@Override
	public SVExprString duplicate() {
		SVExprString ret = new SVExprString(fExprStr);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		SVExprString o = (SVExprString)other;
		fExprStr = o.fExprStr;
	}
}
