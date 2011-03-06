/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVExprType;

public class SVDBConstraintDistListStmt extends SVDBStmt {
	private List<SVExpr>						fLHS;
	private List<SVDBConstraintDistItemStmt>	fDistItems;
	
	public SVDBConstraintDistListStmt() {
		super(SVDBItemType.ConstraintDistListStmt);
		fLHS = new ArrayList<SVExpr>();
		fDistItems = new ArrayList<SVDBConstraintDistItemStmt>();
	}
	
	public void addLHS(SVExpr lhs) {
		fLHS.add(lhs);
	}
	
	public List<SVExpr> getLHS() {
		return fLHS;
	}
	
	public List<SVDBConstraintDistItemStmt> getDistItems() {
		return fDistItems;
	}
	
	public void addDistItem(SVDBConstraintDistItemStmt item) {
		fDistItems.add(item);
	}
	
	public SVDBConstraintDistListStmt duplicate() {
		SVDBConstraintDistListStmt ret = new SVDBConstraintDistListStmt();
		ret.getDistItems().addAll(fDistItems);
		
		return ret;
	}

}
