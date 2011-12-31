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

public class SVDBCondExpr extends SVDBExpr {
	private SVDBExpr			fLhs;
	private SVDBExpr			fMhs;
	private SVDBExpr			fRhs;
	
	public SVDBCondExpr() {
		this(null, null, null);
	}
	
	public SVDBCondExpr(SVDBExpr lhs, SVDBExpr mhs, SVDBExpr rhs) {
		super(SVDBItemType.CondExpr);
		
		fLhs = lhs;
		fMhs = mhs;
		fRhs = rhs;
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public SVDBExpr getMhs() {
		return fMhs;
	}
	
	public SVDBExpr getRhs() {
		return fRhs;
	}
	
	public SVDBCondExpr duplicate() {
		return (SVDBCondExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		SVDBCondExpr ce = (SVDBCondExpr)other;
		
		fLhs = (SVDBExpr)ce.fLhs.duplicate();
		fMhs = (SVDBExpr)ce.fMhs.duplicate();
		fRhs = (SVDBExpr)ce.fRhs.duplicate();
	}

}
