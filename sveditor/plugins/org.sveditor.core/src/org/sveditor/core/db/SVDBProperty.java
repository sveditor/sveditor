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

public class SVDBProperty extends SVDBScopeItem {
	public SVDBExpr					fExpr;
	public List<SVDBParamPortDecl>		fPortList;
	
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
