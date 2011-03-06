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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;


public class SVDBConstraintIfStmt extends SVDBStmt {
	private SVExpr					fIfExpr;
	private SVDBStmt				fConstraint;
	private SVDBStmt				fElse;
	private boolean					fElseIf;
	
	public SVDBConstraintIfStmt(
			SVExpr 					expr,
			SVDBStmt				constraint,
			SVDBStmt				else_expr,
			boolean					else_if) {
		super(SVDBItemType.ConstraintIfStmt);
		fIfExpr 	= expr;
		fConstraint = constraint;
		fElse		= else_expr;
		fElseIf 	= else_if;
	}
	
	public SVExpr getExpr() {
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
