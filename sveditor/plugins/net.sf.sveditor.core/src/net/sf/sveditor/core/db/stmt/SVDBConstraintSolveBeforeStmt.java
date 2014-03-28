/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

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
