/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;


public class SVDBUnaryExpr extends SVDBExpr {
	public SVDBExpr				fExpr;
	public String					fOp;
	
	public SVDBUnaryExpr() {
		this(null, null);
	}
	
	public SVDBUnaryExpr(String op, SVDBExpr expr) {
		super(SVDBItemType.UnaryExpr);
		
		fOp = op;
		fExpr = expr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setOp(String op) {
		fOp = op;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVDBUnaryExpr duplicate() {
		return (SVDBUnaryExpr)super.duplicate();
	}

}
