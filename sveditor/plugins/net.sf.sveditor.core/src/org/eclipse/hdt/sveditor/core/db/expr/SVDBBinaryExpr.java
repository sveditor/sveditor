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

/** Change 2 */

public class SVDBBinaryExpr extends SVDBExpr {
	public SVDBExpr				fLhs;
	public String					fOp;
	public SVDBExpr				fRhs;
	
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
