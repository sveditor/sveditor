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
import net.sf.sveditor.core.db.expr.SVExpr;


public class SVDBConstraintDistItemStmt extends SVDBStmt {
	private SVExpr				fLHS;
	private SVExpr				fRHS;
	private boolean				fIsDist;
	
	public SVDBConstraintDistItemStmt() {
		super(SVDBItemType.ConstraintDistListItem);
	}
	
	public void setLHS(SVExpr lhs) {
		fLHS = lhs;
	}
	
	public SVExpr getLHS() {
		return fLHS;
	}
	
	public void setRHS(SVExpr rhs) {
		fRHS = rhs;
	}
	
	public SVExpr getRHS() {
		return fRHS;
	}
	
	public boolean isDist() {
		return fIsDist;
	}
	
	public void setIsDist(boolean is_dist) {
		fIsDist = is_dist;
	}
	
	public SVDBConstraintDistItemStmt duplicate() {
		SVDBConstraintDistItemStmt ret = new SVDBConstraintDistItemStmt();
		ret.setLHS((SVExpr)fLHS.duplicate());
		ret.setRHS((SVExpr)fRHS.duplicate());
		ret.setIsDist(fIsDist);
		
		return ret;
	}

}
