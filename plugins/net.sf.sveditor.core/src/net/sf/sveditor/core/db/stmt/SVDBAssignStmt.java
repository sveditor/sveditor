/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

public class SVDBAssignStmt extends SVDBStmt {
	public SVDBExpr			fLHS;
	public String			fOp;
	public SVDBExpr			fDelayExpr;
	public SVDBExpr			fRHS;
	
	public SVDBAssignStmt() {
		super(SVDBItemType.AssignStmt);
	}
	
	public void setLHS(SVDBExpr lhs) {
		fLHS = lhs;
	}
	
	public SVDBExpr getLHS() {
		return fLHS;
	}
	
	public void setOp(String op) {
		fOp = op;
	}
	
	public String getOp() {
		return fOp;
	}
	
	public void setRHS(SVDBExpr expr) {
		fRHS = expr;
	}
	
	public SVDBExpr getRHS() {
		return fRHS;
	}
	
	public void setDelayExpr(SVDBExpr expr) {
		fDelayExpr = expr;
	}
	
	public SVDBExpr getDelayExpr() {
		return fDelayExpr;
	}

}
