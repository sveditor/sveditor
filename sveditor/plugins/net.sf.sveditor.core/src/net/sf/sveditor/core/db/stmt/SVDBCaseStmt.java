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


package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCaseStmt extends SVDBStmt {
	
	public enum CaseType {
		Case,
		Casex,
		Casez,
		Randcase
	};
	
	public CaseType						fCaseType;
	public SVDBExpr						fExpr;
	public List<SVDBCaseItem>			fCaseItemList;
	
	public SVDBCaseStmt() {
		this(CaseType.Case);
	}
	
	public SVDBCaseStmt(CaseType type) {
		super(SVDBItemType.CaseStmt);
		fCaseItemList = new ArrayList<SVDBCaseItem>();
		fCaseType = type;
	}
	
	public CaseType getCaseType() {
		return fCaseType;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public List<SVDBCaseItem> getCaseItemList() {
		return fCaseItemList;
	}
	
	public void addCaseItem(SVDBCaseItem item) {
		fCaseItemList.add(item);
	}

}
