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

public class SVAssignExpr extends SVExpr {
	private SVExpr					fLhs;
	private String					fOp;
	private SVExpr					fRhs;
	
	public SVAssignExpr(
			SVExpr			lhs,
			String			op,
			SVExpr			rhs) {
		super(SVExprType.Assign);
		
		fLhs = lhs;
		fOp  = op;
		fRhs = rhs;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVExpr getRhs() {
		return fRhs;
	}

}
