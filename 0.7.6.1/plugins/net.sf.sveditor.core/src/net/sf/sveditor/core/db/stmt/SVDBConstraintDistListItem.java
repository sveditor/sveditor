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

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;


public class SVDBConstraintDistListItem extends SVDBStmt {
	private SVDBExpr				fLHS;
	private SVDBExpr				fRHS;
	private boolean				fIsDist;
	
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
