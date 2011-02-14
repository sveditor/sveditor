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


public class SVUnaryExpr extends SVExpr {
	private SVExpr					fExpr;
	private String					fOp;
	
	public SVUnaryExpr(String op, SVExpr expr) {
		super(SVExprType.Unary);
		
		fOp = op;
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVUnaryExpr duplicate() {
		return new SVUnaryExpr(fOp, (SVExpr)fExpr.duplicate());
	}

}
