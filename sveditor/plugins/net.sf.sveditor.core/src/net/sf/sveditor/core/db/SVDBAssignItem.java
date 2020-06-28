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
package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAssignItem extends SVDBChildItem {
	public SVDBExpr				fLHS;
	public SVDBExpr				fRHS;

	public SVDBAssignItem() {
		super(SVDBItemType.AssignItem);
	}
	
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	
	public void setRHS(SVDBExpr rhs) {
		fRHS = rhs;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
}
