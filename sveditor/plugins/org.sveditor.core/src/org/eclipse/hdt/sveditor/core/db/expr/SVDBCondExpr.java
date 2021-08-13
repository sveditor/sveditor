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

import org.eclipse.hdt.sveditor.core.db.SVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBCondExpr extends SVDBExpr {
	public SVDBExpr			fLhs;
	public SVDBExpr			fMhs;
	public SVDBExpr			fRhs;
	
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
