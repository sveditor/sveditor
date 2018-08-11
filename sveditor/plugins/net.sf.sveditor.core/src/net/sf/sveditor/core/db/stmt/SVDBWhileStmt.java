/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBWhileStmt extends SVDBBodyStmt {
	public SVDBExpr				fCond;
	
	public SVDBWhileStmt() {
		super(SVDBItemType.WhileStmt);
	}
	
	public SVDBWhileStmt(SVDBExpr cond) {
		super(SVDBItemType.WhileStmt);
		fCond = cond;
	}
	
	public SVDBExpr getExpr() {
		return fCond;
	}
	
	public void setExpr(SVDBExpr expr) {
		fCond = expr;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_while_stmt(this);
	}
	
}
