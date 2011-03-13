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

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBAssign extends SVDBStmt {
	
	private SVDBExpr				fLHS;
	private SVDBExpr				fDelay;
	private SVDBExpr				fRHS;
	
	public SVDBAssign() {
		super(SVDBItemType.Assign);
	}
	
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	
	public void setDelay(SVDBExpr delay) {
		fDelay = delay;
	}
	
	public SVDBExpr getDelay() {
		return fDelay;
	}
	
	public void setRHS(SVDBExpr rhs) {
		fRHS = rhs;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
	
	public SVDBAssign duplicate() {
		SVDBAssign ret = new SVDBAssign();
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
	}

}
