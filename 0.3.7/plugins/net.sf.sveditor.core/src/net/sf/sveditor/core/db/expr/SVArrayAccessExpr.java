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

public class SVArrayAccessExpr extends SVExpr {
	private SVExpr				fLhs;
	private SVExpr				fLow;
	private SVExpr				fHigh;
	
	public SVArrayAccessExpr(SVExpr lhs, SVExpr low, SVExpr high) {
		super(SVExprType.ArrayAccess);
		
		fLhs   = lhs;
		fLow   = low;
		fHigh  = high;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public SVExpr getLow() {
		return fLow;
	}
	
	public SVExpr getHigh() {
		return fHigh;
	}
	
	public SVDBItemBase duplicate() {
		SVArrayAccessExpr ret = new SVArrayAccessExpr(fLhs, fLow, fHigh);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		SVArrayAccessExpr aa = (SVArrayAccessExpr)other;

		super.init(other);

		fLhs = aa.fLhs;
		fLow = aa.fLow;
		fHigh = aa.fHigh;
	}
	
}
