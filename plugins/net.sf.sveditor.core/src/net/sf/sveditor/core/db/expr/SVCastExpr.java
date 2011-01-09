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

public class SVCastExpr extends SVExpr {
	private SVExpr					fCastType;
	private SVExpr					fExpr;
	
	public SVCastExpr(SVExpr cast_type, SVExpr expr) {
		super(SVExprType.Cast);
		
		fCastType = cast_type;
		fExpr = expr;
	}
	
	public SVExpr getCastType() {
		return fCastType;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public SVCastExpr duplicate() {
		SVCastExpr ret = new SVCastExpr(
				(SVExpr)fCastType.duplicate(), 
				(SVExpr)fExpr.duplicate());
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVCastExpr ce = (SVCastExpr)other;
		fCastType = (SVExpr)ce.fCastType.duplicate();
		fExpr     = (SVExpr)ce.fExpr.duplicate();
	}
	
}
