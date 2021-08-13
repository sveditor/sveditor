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

public class SVDBAssignExpr extends SVDBExpr {
	public SVDBExpr					fLhs;
	public String						fOp;
	public SVDBExpr					fRhs;
	
	public SVDBAssignExpr() {
		this(null, null, null);
	}
	
	public SVDBAssignExpr(
			SVDBExpr			lhs,
			String				op,
			SVDBExpr			rhs) {
		super(SVDBItemType.AssignExpr);
		
		fLhs = lhs;
		fOp  = op;
		fRhs = rhs;
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public void setLhs(SVDBExpr lhs) {
		fLhs = lhs;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public void setOp(String op) {
		fOp = op;
	}
	
	public SVDBExpr getRhs() {
		return fRhs;
	}
	
	public void setRhs(SVDBExpr rhs) {
		fRhs = rhs;
	}

	public SVDBAssignExpr duplicate() {
		return (SVDBAssignExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		SVDBAssignExpr ae = (SVDBAssignExpr)other;
		
		super.init(other);
		
		fLhs = ae.fLhs;
		fOp  = ae.fOp;
		fRhs = ae.fRhs;
	}
}
