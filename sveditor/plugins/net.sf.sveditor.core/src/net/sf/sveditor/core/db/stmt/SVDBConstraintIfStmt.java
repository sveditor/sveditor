/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;


public class SVDBConstraintIfStmt extends SVDBStmt {
	public SVDBExpr					fIfExpr;
	public SVDBStmt				fConstraint;
	public SVDBStmt				fElse;
	public boolean					fElseIf;
	
	public SVDBConstraintIfStmt() {
		super(SVDBItemType.ConstraintIfStmt);
	}
	
	public SVDBConstraintIfStmt(
			SVDBExpr 					expr,
			SVDBStmt				constraint,
			SVDBStmt				else_expr,
			boolean					else_if) {
		super(SVDBItemType.ConstraintIfStmt);
		fIfExpr 	= expr;
		fConstraint = constraint;
		fElse		= else_expr;
		fElseIf 	= else_if;
	}
	
	public SVDBExpr getExpr() {
		return fIfExpr;
	}
	
	public SVDBStmt getConstraint() {
		return fConstraint;
	}
	
	public SVDBStmt getElseClause() {
		return fElse;
	}
	
	public boolean isElseIf() {
		return fElseIf;
	}
	
	/*
	public SVDBConstraintIfStmt duplicate() {
		return new SVDBConstraintIfStmt(
				(SVExpr)fIfExpr.duplicate(),
				(SVDBConstraintSetStmt)fConstraint.duplicate(),
				(SVExpr)((fElse != null)?fElse.duplicate():null), 
				fElseIf);
	}
	 */

}
