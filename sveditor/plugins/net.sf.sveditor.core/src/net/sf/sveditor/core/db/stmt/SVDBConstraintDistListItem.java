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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;


public class SVDBConstraintDistListItem extends SVDBStmt {
	public SVDBExpr				fLHS;
	public SVDBExpr				fRHS;
	public boolean				fIsDist;
	
	public SVDBConstraintDistListItem() {
		super(SVDBItemType.ConstraintDistListItem);
	}
	
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	
	public void setRHS(SVDBExpr rhs) {
		fRHS = rhs;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
	
	public boolean isDist() {
		return fIsDist;
	}
	
	public void setIsDist(boolean is_dist) {
		fIsDist = is_dist;
	}
	
	public SVDBConstraintDistListItem duplicate() {
		return (SVDBConstraintDistListItem)super.duplicate();
	}

}
