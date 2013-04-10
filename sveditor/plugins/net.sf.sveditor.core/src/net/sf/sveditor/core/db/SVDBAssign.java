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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBAssign extends SVDBStmt implements ISVDBAddChildItem {
	
	public SVDBExpr					fDelay;
	public List<SVDBAssignItem>		fAssignList;

	
	public SVDBAssign() {
		super(SVDBItemType.Assign);
		fAssignList = new ArrayList<SVDBAssignItem>();
	}
	
	public List<SVDBAssignItem> getAssignList() {
		return fAssignList;
	}
	
	/*
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	 */
	
	@Override
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fAssignList.add((SVDBAssignItem)item);
	}

	public void setDelay(SVDBExpr delay) {
		fDelay = delay;
	}
	
	public SVDBExpr getDelay() {
		return fDelay;
	}

	/*
	public void setRHS(SVDBExpr rhs) {
		fRHS = rhs;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
	 */
	
	public SVDBAssign duplicate() {
		return (SVDBAssign)SVDBItemUtils.duplicate(this);
	}
}
