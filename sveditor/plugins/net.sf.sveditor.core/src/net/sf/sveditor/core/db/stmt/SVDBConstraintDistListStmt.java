/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConstraintDistListStmt extends SVDBStmt {
	public List<SVDBExpr>						fLHS;
	public List<SVDBConstraintDistListItem>		fDistItems;
	
	public SVDBConstraintDistListStmt() {
		super(SVDBItemType.ConstraintDistListStmt);
		fLHS = new ArrayList<SVDBExpr>();
		fDistItems = new ArrayList<SVDBConstraintDistListItem>();
	}
	
	public void addLHS(SVDBExpr lhs) {
		fLHS.add(lhs);
	}
	
	public List<SVDBExpr> getLHS() {
		return fLHS;
	}
	
	public List<SVDBConstraintDistListItem> getDistItems() {
		return fDistItems;
	}
	
	public void addDistItem(SVDBConstraintDistListItem item) {
		fDistItems.add(item);
	}
	
	public SVDBConstraintDistListStmt duplicate() {
		return (SVDBConstraintDistListStmt)super.duplicate();
	}

}
