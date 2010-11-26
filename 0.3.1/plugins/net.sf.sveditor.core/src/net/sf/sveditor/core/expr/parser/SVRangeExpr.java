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

public class SVRangeExpr extends SVExpr {
	
	private SVExpr				fLeft;
	private SVExpr				fRight;
	
	public SVRangeExpr(SVExpr left, SVExpr right) {
		super(SVExprType.Range);
		fLeft  = left;
		fRight = right;
	}
	
	public SVExpr getLeft() {
		return fLeft;
	}
	
	public SVExpr getRight() {
		return fRight;
	}
	
	public SVExpr duplicate() {
		return new SVRangeExpr(fLeft.duplicate(), fRight.duplicate());
	}

}
