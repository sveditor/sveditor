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
import net.sf.sveditor.core.db.SVDBItemType;

/** Change 2 */

public class SVDBBinaryExpr extends SVDBExpr {
	SVDBExpr				fLhs;
	String					fOp;
	SVDBExpr				fRhs;
	
	public SVDBBinaryExpr() {
		this(null, null, null);
	}
	
	public SVDBBinaryExpr(SVDBExpr lhs, String op, SVDBExpr rhs) {
		super(SVDBItemType.BinaryExpr);
		
		fLhs = lhs;
		fOp = op;
		fRhs = rhs;
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVDBExpr getRhs() {
		return fRhs;
	}
	
	public SVDBBinaryExpr duplicate() {
		return (SVDBBinaryExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBBinaryExpr be = (SVDBBinaryExpr)other;
		
		fLhs = (SVDBExpr)be.fLhs.duplicate();
		fOp  = be.fOp;
		fRhs = (SVDBExpr)be.fRhs.duplicate();
	}

}
