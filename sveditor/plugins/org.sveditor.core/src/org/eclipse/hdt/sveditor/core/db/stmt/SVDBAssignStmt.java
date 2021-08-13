/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

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
