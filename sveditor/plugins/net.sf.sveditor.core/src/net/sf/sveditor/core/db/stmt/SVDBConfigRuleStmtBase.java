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
package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigRuleStmtBase extends SVDBStmt {
	public boolean					fIsLibList;
	public List<SVDBExpr>			fLibUseList;
	public SVDBExpr					fLibCellId;
	public SVDBParamValueAssignList	fParamValueAssign;
	
	public SVDBConfigRuleStmtBase(SVDBItemType type) {
		super(type);
		fLibUseList = new ArrayList<SVDBExpr>();
	}
	
	public void addLib(SVDBExpr lib) {
		fLibUseList.add(lib);
	}
	
	public void setLibCellId(SVDBExpr id) {
		fLibCellId = id;
	}
	
	public void setParamAssign(SVDBParamValueAssignList assign) {
		fParamValueAssign = assign;
	}

}
