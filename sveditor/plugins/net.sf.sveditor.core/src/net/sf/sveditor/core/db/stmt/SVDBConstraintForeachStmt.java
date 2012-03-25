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

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConstraintForeachStmt extends SVDBStmt {
	public SVDBExpr				fExpr;
	public SVDBStmt			fStmt;
	
	public SVDBConstraintForeachStmt() {
		super(SVDBItemType.ConstraintForeachStmt);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setStmt(SVDBStmt stmt) {
		fStmt = stmt;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}

}
