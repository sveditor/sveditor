/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.db.stmt;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBExprStmt extends SVDBStmt {
	public SVDBExpr				fExpr;
	
	public SVDBExprStmt() {
		super(SVDBItemType.ExprStmt);
	}
	
	public SVDBExprStmt(SVDBExpr expr) {
		super(SVDBItemType.ExprStmt);
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}

}
