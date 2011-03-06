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

import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVRandomizeCallExpr extends SVTFCallExpr {
	private SVDBStmt				fWithBlock;
	
	public SVRandomizeCallExpr(SVExpr target, String name, SVExpr args[]) {
		super(target, name, args);
		fExprType = SVExprType.RandomizeCall;
	}
	
	public void setWithBlock(SVDBStmt with) {
		fWithBlock = with;
	}
	
	public SVDBStmt getWithBlock() {
		return fWithBlock;
	}
	
}
