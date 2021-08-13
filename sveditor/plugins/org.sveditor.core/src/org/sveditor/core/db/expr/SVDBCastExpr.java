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


package org.sveditor.core.db.expr;

import org.sveditor.core.db.SVDBItemBase;
import org.sveditor.core.db.SVDBItemType;

public class SVDBCastExpr extends SVDBExpr {
	public SVDBExpr					fCastType;
	public SVDBExpr					fExpr;
	
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
		return (SVDBCastExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBCastExpr ce = (SVDBCastExpr)other;
		fCastType = (SVDBExpr)ce.fCastType.duplicate();
		fExpr     = (SVDBExpr)ce.fExpr.duplicate();
	}
	
}
