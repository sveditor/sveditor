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

public class SVDBRandseqStmt extends SVDBStmt {
	
	public String							fName;
	public List<SVDBParamPortDecl>			fParams;
	public List<SVDBRandseqProdStmt>		fRandseqProdStmtList;

	public SVDBRandseqStmt() {
		super(SVDBItemType.RandseqStmt);
		fParams = new ArrayList<SVDBParamPortDecl>();
		fRandseqProdStmtList = new ArrayList<SVDBRandseqProdStmt>();
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void addRandseqProdStmt (SVDBRandseqProdStmt item)  {
		fRandseqProdStmtList.add(item);
	}
	
	
	public void setTfPortList(List<SVDBParamPortDecl> params) {
		fParams = params;
		if (params != null)  {
			for (SVDBParamPortDecl p : params) {
				p.setParent(this);
			}
		}
	}
	

}
