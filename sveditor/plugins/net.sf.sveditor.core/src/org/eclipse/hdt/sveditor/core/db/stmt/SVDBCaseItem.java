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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBCaseItem extends SVDBBodyStmt {
	public List<SVDBExpr>		fCaseExprList;
	
	public SVDBCaseItem() {
		super(SVDBItemType.CaseItem);
		fCaseExprList = new ArrayList<SVDBExpr>();
	}
	
	public List<SVDBExpr> getExprList() {
		return fCaseExprList;
	}
	
	public void addExpr(SVDBExpr expr) {
		fCaseExprList.add(expr);
	}
	

}
