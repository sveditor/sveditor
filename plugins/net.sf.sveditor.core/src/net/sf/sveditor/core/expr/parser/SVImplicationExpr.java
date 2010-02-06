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

public class SVImplicationExpr extends SVConstraintExpr {
	
	private SVExpr					fExpr;
	private SVConstraintSetExpr		fConstraint;
	
	
	public SVImplicationExpr(SVExpr expr, SVConstraintSetExpr constraint) {
		super(SVExprType.Implication);
		fExpr 		= expr;
		fConstraint = constraint;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public SVConstraintSetExpr getConstraintSet() {
		return fConstraint;
	}

}
