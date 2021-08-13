/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.db.expr;

import org.sveditor.core.db.SVDBItemType;

public class SVDBPropertyIfStmt extends SVDBExpr {
	public SVDBExpr				fExpr;
	public SVDBExpr				fIfExpr;
	public SVDBExpr				fElseExpr;
	
	public SVDBPropertyIfStmt() {
		super(SVDBItemType.PropertyIfStmt);
	}

	public void setIfExpr(SVDBExpr expr) {
		fIfExpr = expr;
	}
	
	public SVDBExpr getIfExpr() {
		return fIfExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setElseExpr(SVDBExpr expr) {
		fElseExpr = expr;
	}
	
	public SVDBExpr getElseExpr() {
		return fElseExpr;
	}
}
