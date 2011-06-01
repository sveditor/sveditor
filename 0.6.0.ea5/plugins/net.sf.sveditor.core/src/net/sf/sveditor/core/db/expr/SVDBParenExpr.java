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


public class SVDBParenExpr extends SVDBExpr {
	public SVDBExpr				fExpr;
	
	public SVDBParenExpr() {
		this(null);
	}
	
	public SVDBParenExpr(SVDBExpr expr) {
		super(SVDBItemType.ParenExpr);
		
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public SVDBParenExpr duplicate() {
		return (SVDBParenExpr)super.duplicate();
	}

}
