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


public class SVDBIncDecExpr extends SVDBExpr {
	public SVDBExpr				fExpr;
	public String					fOp;
	
	public SVDBIncDecExpr() {
		this(null, null);
	}
	
	public SVDBIncDecExpr(String op, SVDBExpr expr) {
		super(SVDBItemType.IncDecExpr);
		
		fExpr = expr;
		fOp   = op;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public SVDBIncDecExpr duplicate() {
		return (SVDBIncDecExpr)super.duplicate();
	}

}
