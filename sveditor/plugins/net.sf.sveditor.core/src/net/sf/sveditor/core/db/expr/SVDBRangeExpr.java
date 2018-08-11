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

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;


public class SVDBRangeExpr extends SVDBExpr {
	
	public SVDBExpr				fLeft;
	public SVDBExpr				fRight;
	
	public SVDBRangeExpr() {
		this(null, null);
	}
	
	public SVDBRangeExpr(SVDBExpr left, SVDBExpr right) {
		super(SVDBItemType.RangeExpr);
		fLeft  = left;
		fRight = right;
	}
	
	public SVDBExpr getLeft() {
		return fLeft;
	}
	
	public SVDBExpr getRight() {
		return fRight;
	}
	
	public SVDBRangeExpr duplicate() {
		return (SVDBRangeExpr)super.duplicate();
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_range_expr(this);
	}
}
