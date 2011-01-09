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

public class SVFieldAccessExpr extends SVExpr {
	private SVExpr 					fExpr;
	private boolean					fStaticRef;
	private String					fId;

	public SVFieldAccessExpr(SVExpr expr, boolean static_ref, String id) {
		super(SVExprType.FieldAccess);
		
		fExpr = expr;
		fStaticRef = static_ref;
		fId   = id;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public boolean isStaticRef() {
		return fStaticRef;
	}
	
	public String getId() {
		return fId;
	}
	
	public SVDBItemBase duplicate() {
		return new SVFieldAccessExpr((SVExpr)fExpr.duplicate(), fStaticRef, fId);
	}
}
