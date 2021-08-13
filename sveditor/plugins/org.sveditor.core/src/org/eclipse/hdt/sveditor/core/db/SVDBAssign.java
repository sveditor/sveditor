/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBStmt;

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
