/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
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
