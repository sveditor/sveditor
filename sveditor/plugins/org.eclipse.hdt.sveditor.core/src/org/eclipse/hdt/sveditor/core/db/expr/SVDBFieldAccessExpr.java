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


public class SVDBFieldAccessExpr extends SVDBExpr {
	public SVDBExpr 					fExpr;
	public boolean						fStaticRef;
	public SVDBExpr					fLeaf;

	public SVDBFieldAccessExpr() {
		this(null, false, null);
	}
	
	public SVDBFieldAccessExpr(SVDBExpr expr, boolean static_ref, SVDBExpr leaf) {
		super(SVDBItemType.FieldAccessExpr);
		
		fExpr = expr;
		fStaticRef = static_ref;
		fLeaf = leaf;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public boolean isStaticRef() {
		return fStaticRef;
	}
	
	public SVDBExpr getLeaf() {
		return fLeaf;
	}
	
	public SVDBFieldAccessExpr duplicate() {
		return (SVDBFieldAccessExpr)super.duplicate();
	}
}
