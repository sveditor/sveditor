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
package org.eclipse.hdt.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBBodyStmt;

public class SVDBPropertyCaseItem extends SVDBBodyStmt {
	public List<SVDBExpr>				fExprList;
	public SVDBExpr						fStmt;
	
	public SVDBPropertyCaseItem() {
		super(SVDBItemType.PropertyCaseItem);
		fExprList = new ArrayList<SVDBExpr>();
	}
	
	public void addExpr(SVDBExpr expr) {
		fExprList.add(expr);
	}
	
	public void setStmt(SVDBExpr stmt) {
		fStmt = stmt;
	}
	
	public SVDBExpr getStmt() {
		return fStmt;
	}
	
}
