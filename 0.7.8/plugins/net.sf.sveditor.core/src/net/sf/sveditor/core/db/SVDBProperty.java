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

public class SVDBProperty extends SVDBScopeItem {
	SVDBExpr					fExpr;
	List<SVDBParamPortDecl>		fPortList;
	
	public SVDBProperty() {
		this("");
	}
	
	public SVDBProperty(String name) {
		super(name, SVDBItemType.Property);
		fPortList = new ArrayList<SVDBParamPortDecl>();
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}

	public void addPropertyPort(SVDBParamPortDecl p) {
		fPortList.add(p);
	}
	
	public List<SVDBParamPortDecl> getPropertyPortList() {
		return fPortList;
	}
}
