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

public class SVCondExpr extends SVExpr {
	private SVExpr			fLhs;
	private SVExpr			fMhs;
	private SVExpr			fRhs;
	
	public SVCondExpr(SVExpr lhs, SVExpr mhs, SVExpr rhs) {
		super(SVExprType.Cond);
		
		fLhs = lhs;
		fMhs = mhs;
		fRhs = rhs;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public SVExpr getMhs() {
		return fMhs;
	}
	
	public SVExpr getRhs() {
		return fRhs;
	}
	
	public SVCondExpr duplicate() {
		SVCondExpr ret = new SVCondExpr(
				(SVExpr)fLhs.duplicate(), 
				(SVExpr)fMhs.duplicate(), 
				(SVExpr)fRhs.duplicate());
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		SVCondExpr ce = (SVCondExpr)other;
		
		fLhs = (SVExpr)ce.fLhs.duplicate();
		fMhs = (SVExpr)ce.fMhs.duplicate();
		fRhs = (SVExpr)ce.fRhs.duplicate();
	}

}
