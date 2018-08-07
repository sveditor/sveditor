/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


public class SVDBFieldAccessExpr extends SVDBExpr {
	public SVDBExpr 					fExpr;
	public boolean						fStaticRef;
	public SVDBExpr						fLeaf;

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
