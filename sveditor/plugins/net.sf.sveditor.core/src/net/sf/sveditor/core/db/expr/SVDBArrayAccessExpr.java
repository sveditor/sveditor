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

import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArrayAccessExpr extends SVDBExpr {
	public SVDBExpr				fLhs;
	public SVDBExpr				fLow;
	public SVDBExpr				fHigh;
	
	public SVDBArrayAccessExpr() {
		this(null, null, null);
	}
	
	public SVDBArrayAccessExpr(SVDBExpr lhs, SVDBExpr low, SVDBExpr high) {
		super(SVDBItemType.ArrayAccessExpr);
		
		fLhs   = lhs;
		fLow   = low;
		fHigh  = high;
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public SVDBExpr getLow() {
		return fLow;
	}
	
	public SVDBExpr getHigh() {
		return fHigh;
	}
	
	public SVDBArrayAccessExpr duplicate() {
		return (SVDBArrayAccessExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		SVDBArrayAccessExpr aa = (SVDBArrayAccessExpr)other;

		super.init(other);

		fLhs = aa.fLhs;
		fLow = aa.fLow;
		fHigh = aa.fHigh;
	}
	
}
