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
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCastExpr extends SVDBExpr {
	private SVDBExpr					fCastType;
	private SVDBExpr					fExpr;
	
	public SVDBCastExpr() {
		this(null, null);
	}
	
	public SVDBCastExpr(SVDBExpr cast_type, SVDBExpr expr) {
		super(SVDBItemType.CastExpr);
		
		fCastType = cast_type;
		fExpr = expr;
	}
	
	public SVDBExpr getCastType() {
		return fCastType;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public SVDBCastExpr duplicate() {
		SVDBCastExpr ret = new SVDBCastExpr(
				(SVDBExpr)fCastType.duplicate(), 
				(SVDBExpr)fExpr.duplicate());
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBCastExpr ce = (SVDBCastExpr)other;
		fCastType = (SVDBExpr)ce.fCastType.duplicate();
		fExpr     = (SVDBExpr)ce.fExpr.duplicate();
	}
	
}
