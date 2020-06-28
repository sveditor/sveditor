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


package org.eclipse.hdt.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

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
