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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBSequence extends SVDBScopeItem {
	private SVDBExpr					fExpr;
	private List<SVDBParamPortDecl>		fPortList;
	private List<SVDBVarDeclStmt>		fVarDeclList;
	
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
