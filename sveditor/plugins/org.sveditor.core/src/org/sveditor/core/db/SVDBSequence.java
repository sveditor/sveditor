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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.expr.SVDBExpr;
import org.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBSequence extends SVDBScopeItem {
	public SVDBExpr					fExpr;
	public List<SVDBParamPortDecl>		fPortList;
	public List<SVDBVarDeclStmt>		fVarDeclList;
	
	public SVDBSequence() {
		this("");
	}
	
	public SVDBSequence(String name) {
		super(name, SVDBItemType.Sequence);
		fPortList = new ArrayList<SVDBParamPortDecl>();
		fVarDeclList = new ArrayList<SVDBVarDeclStmt>();
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}

	public void addPort(SVDBParamPortDecl port) {
		fPortList.add(port);
	}
	
	public List<SVDBParamPortDecl> getPortList() {
		return fPortList;
	}
	
	public void addVarDecl(SVDBVarDeclStmt decl) {
		fVarDeclList.add(decl);
	}
	
	public List<SVDBVarDeclStmt> getVarDeclList() {
		return fVarDeclList;
	}
}
