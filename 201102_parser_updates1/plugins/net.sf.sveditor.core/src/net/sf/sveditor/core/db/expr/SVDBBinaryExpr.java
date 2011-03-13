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

public class SVDBBinaryExpr extends SVDBExpr {
	private SVDBExpr				fLhs;
	private String					fOp;
	private SVDBExpr				fRhs;
	
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
		SVDBBinaryExpr ret = new SVDBBinaryExpr(
				(SVDBExpr)fLhs.duplicate(), fOp, 
				(SVDBExpr)fRhs.duplicate());
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBBinaryExpr be = (SVDBBinaryExpr)other;
		
		fLhs = (SVDBExpr)be.fLhs.duplicate();
		fOp  = be.fOp;
		fRhs = (SVDBExpr)be.fRhs.duplicate();
	}

}
