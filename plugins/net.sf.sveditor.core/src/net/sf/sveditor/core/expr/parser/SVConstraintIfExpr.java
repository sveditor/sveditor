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


package net.sf.sveditor.core.expr.parser;

public class SVConstraintIfExpr extends SVConstraintExpr {
	private SVExpr					fIfExpr;
	private SVConstraintSetExpr		fConstraint;
	private SVExpr					fElse;
	private boolean					fElseIf;
	
	public SVConstraintIfExpr(
			SVExpr 					expr,
			SVConstraintSetExpr		constraint,
			SVExpr					else_expr,
			boolean					else_if) {
		super(SVExprType.ConstraintIf);
		fIfExpr 	= expr;
		fConstraint = constraint;
		fElse		= else_expr;
		fElseIf 	= else_if;
	}
	
	public SVExpr getExpr() {
		return fIfExpr;
	}
	
	public SVConstraintSetExpr getConstraint() {
		return fConstraint;
	}
	
	public SVExpr getElseClause() {
		return fElse;
	}
	
	public boolean isElseIf() {
		return fElseIf;
	}
	
	public SVExpr duplicate() {
		return new SVConstraintIfExpr(fIfExpr.duplicate(),
				(SVConstraintSetExpr)fConstraint.duplicate(),
				(fElse != null)?fElse.duplicate():null, fElseIf);
	}

}
