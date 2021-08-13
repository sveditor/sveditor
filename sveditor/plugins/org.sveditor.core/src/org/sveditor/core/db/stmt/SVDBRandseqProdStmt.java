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
package org.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBTypeInfo;
import org.sveditor.core.db.expr.SVDBExpr;

public class SVDBRandseqProdStmt extends SVDBStmt {
	public SVDBTypeInfo				fRetType;
	public String					fName;
	public List<SVDBParamPortDecl>	fPortList;
	public List<SVDBExpr>			fExprList;
	
	public SVDBRandseqProdStmt() {
		super(SVDBItemType.RandseqProdStmt);
		fExprList = new ArrayList<SVDBExpr>();
		fPortList   = new ArrayList<SVDBParamPortDecl>();
	}
	
	public void setRetType(SVDBTypeInfo type) {
		fRetType = type;
	}
	
	public SVDBTypeInfo getRetType() {
		return fRetType;
	}

	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void addProductionItem(SVDBExpr pi) {
		fExprList.add(pi);
	}
	
	
	public List<SVDBExpr> getProductionItemList() {
		return fExprList;
	}
	
	
	public void setTfPortList(List<SVDBParamPortDecl> params) {
		fPortList = params;
		if (params != null)  {
			for (SVDBParamPortDecl p : params) {
				p.setParent(this);
			}
		}
	}
	
	public List<SVDBParamPortDecl> getTfPortList() {
		return fPortList;
	}
	



}
