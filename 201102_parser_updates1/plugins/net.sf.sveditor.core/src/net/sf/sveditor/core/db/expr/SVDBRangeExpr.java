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

import net.sf.sveditor.core.db.SVDBItemType;


public class SVDBRangeExpr extends SVDBExpr {
	
	private SVDBExpr				fLeft;
	private SVDBExpr				fRight;
	
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
		return new SVDBRangeExpr((SVDBExpr)fLeft.duplicate(), (SVDBExpr)fRight.duplicate());
	}

}
