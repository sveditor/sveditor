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

public class SVRandomizeCallExpr extends SVTFCallExpr {
	private SVConstraintSetExpr				fWithBlock;
	
	public SVRandomizeCallExpr(SVExpr target, String name, SVExpr args[]) {
		super(target, name, args);
		fExprType = SVExprType.RandomizeCall;
	}
	
	public void setWithBlock(SVConstraintSetExpr with) {
		fWithBlock = with;
	}
	
	public SVConstraintSetExpr getWithBlock() {
		return fWithBlock;
	}
	
}
