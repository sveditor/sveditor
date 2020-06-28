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

public class SVDBConstraintSolveBeforeStmt extends SVDBStmt {
	public List<SVDBExpr>				fSolveBeforeList;
	public List<SVDBExpr>				fSolveAfterList;
	
	public SVDBConstraintSolveBeforeStmt() {
		super(SVDBItemType.ConstraintSolveBeforeStmt);
		fSolveBeforeList = new ArrayList<SVDBExpr>();
		fSolveAfterList = new ArrayList<SVDBExpr>();
	}
	
	public List<SVDBExpr> getSolveBeforeList() {
		return fSolveBeforeList;
	}
	
	public void addSolveBefore(SVDBExpr expr) {
		fSolveBeforeList.add(expr);
	}
	
	public List<SVDBExpr> getSolveAfterList() {
		return fSolveAfterList;
	}
	
	public void addSolveAfter(SVDBExpr expr) {
		fSolveAfterList.add(expr);
	}
	
	public SVDBConstraintSolveBeforeStmt duplicate() {
		return (SVDBConstraintSolveBeforeStmt)super.duplicate();
	}

}
