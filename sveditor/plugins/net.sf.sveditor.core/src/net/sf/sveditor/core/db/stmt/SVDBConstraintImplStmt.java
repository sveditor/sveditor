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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;


public class SVDBConstraintImplStmt extends SVDBStmt {
	
	public SVDBExpr					fExpr;
	public SVDBStmt				fConstraint;
	
	public SVDBConstraintImplStmt() {
		super(SVDBItemType.ConstraintImplStmt);
	}
	
	public SVDBConstraintImplStmt(SVDBExpr expr, SVDBStmt constraint) {
		super(SVDBItemType.ConstraintImplStmt);
		fExpr 		= expr;
		fConstraint = constraint;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public SVDBStmt getConstraintSet() {
		return fConstraint;
	}
	
	public SVDBConstraintImplStmt duplicate() {
		return (SVDBConstraintImplStmt)super.duplicate();
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_constraint_impl_stmt(this);;
	}
}
