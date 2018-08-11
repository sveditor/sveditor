/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;

public class SVDBSequenceDistExpr extends SVDBExpr {
	public SVDBExpr					fExpr;
	public SVDBConstraintDistListStmt	fDistExpr;

	public SVDBSequenceDistExpr() {
		super(SVDBItemType.SequenceDistExpr);
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBConstraintDistListStmt getDistExpr() {
		return fDistExpr;
	}
	
	public void setDistExpr(SVDBConstraintDistListStmt dist) {
		fDistExpr = dist;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_sequence_dist_expr(this);
	}
	
}
