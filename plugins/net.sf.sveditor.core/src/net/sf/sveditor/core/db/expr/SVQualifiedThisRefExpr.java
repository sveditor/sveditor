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


public class SVQualifiedThisRefExpr extends SVExpr {
	private SVExpr 				fExpr;
	
	public SVQualifiedThisRefExpr(SVExpr expr) {
		super(SVExprType.QualifiedThisRef);
		
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public SVQualifiedThisRefExpr duplicate() {
		return new SVQualifiedThisRefExpr((SVExpr)fExpr.duplicate());
	}

}
