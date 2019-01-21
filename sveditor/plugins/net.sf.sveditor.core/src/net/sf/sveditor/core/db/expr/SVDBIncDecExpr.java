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

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;


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

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_inc_dec_expr(this);
	}

}
