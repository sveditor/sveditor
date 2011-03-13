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

import net.sf.sveditor.core.db.SVDBItemType;


public class SVDBFieldAccessExpr extends SVDBExpr {
	private SVDBExpr 					fExpr;
	private boolean					fStaticRef;
	private String					fId;

	public SVDBFieldAccessExpr() {
		this(null, false, null);
	}
	
	public SVDBFieldAccessExpr(SVDBExpr expr, boolean static_ref, String id) {
		super(SVDBItemType.FieldAccessExpr);
		
		fExpr = expr;
		fStaticRef = static_ref;
		fId   = id;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public boolean isStaticRef() {
		return fStaticRef;
	}
	
	public String getId() {
		return fId;
	}
	
	public SVDBFieldAccessExpr duplicate() {
		return new SVDBFieldAccessExpr((SVDBExpr)fExpr.duplicate(), fStaticRef, fId);
	}
}
