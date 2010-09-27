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

public class SVFieldAccessExpr extends SVExpr {
	private SVExpr 					fExpr;
	private String					fId;

	public SVFieldAccessExpr(SVExpr expr, String id) {
		super(SVExprType.FieldAccess);
		
		fExpr = expr;
		fId   = id;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public String getId() {
		return fId;
	}
	
	public SVExpr duplicate() {
		return new SVFieldAccessExpr(fExpr.duplicate(), fId);
	}
}
