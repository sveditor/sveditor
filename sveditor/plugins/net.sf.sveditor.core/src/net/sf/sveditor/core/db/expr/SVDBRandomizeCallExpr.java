/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.expr;

import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBRandomizeCallExpr extends SVDBTFCallExpr {
	public SVDBStmt				fWithBlock;
	
	public SVDBRandomizeCallExpr() {
		this(null, null, null);
	}
	public SVDBRandomizeCallExpr(SVDBExpr target, String name, List<SVDBExpr> args) {
		super(SVDBItemType.RandomizeCallExpr, target, name, args);
	}
	
	public void setWithBlock(SVDBStmt with) {
		fWithBlock = with;
	}
	
	public SVDBStmt getWithBlock() {
		return fWithBlock;
	}
	
}
