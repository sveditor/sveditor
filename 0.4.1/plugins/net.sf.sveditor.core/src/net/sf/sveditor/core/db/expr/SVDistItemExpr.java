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


public class SVDistItemExpr extends SVExpr {
	private SVExpr				fLHS;
	private SVExpr				fRHS;
	private boolean				fIsDist;
	
	public SVDistItemExpr() {
		super(SVExprType.DistList);
	}
	
	public void setLHS(SVExpr lhs) {
		fLHS = lhs;
	}
	
	public SVExpr getLHS() {
		return fLHS;
	}
	
	public void setRHS(SVExpr rhs) {
		fRHS = rhs;
	}
	
	public SVExpr getRHS() {
		return fRHS;
	}
	
	public boolean isDist() {
		return fIsDist;
	}
	
	public void setIsDist(boolean is_dist) {
		fIsDist = is_dist;
	}
	
	public SVDistItemExpr duplicate() {
		SVDistItemExpr ret = new SVDistItemExpr();
		ret.setLHS((SVExpr)fLHS.duplicate());
		ret.setRHS((SVExpr)fRHS.duplicate());
		ret.setIsDist(fIsDist);
		
		return ret;
	}

}
