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

import net.sf.sveditor.core.db.SVDBItemBase;

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
	
	public void setLhs(SVExpr lhs) {
		fLhs = lhs;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public void setOp(String op) {
		fOp = op;
	}
	
	public SVExpr getRhs() {
		return fRhs;
	}
	
	public void setRhs(SVExpr rhs) {
		fRhs = rhs;
	}

	public SVDBItemBase duplicate() {
		SVAssignExpr ret = new SVAssignExpr(fLhs, fOp, fRhs);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		SVAssignExpr ae = (SVAssignExpr)other;
		
		super.init(other);
		
		fLhs = ae.fLhs;
		fOp  = ae.fOp;
		fRhs = ae.fRhs;
	}
}
