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


package org.eclipse.hdt.sveditor.core.db.expr;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;


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

}
