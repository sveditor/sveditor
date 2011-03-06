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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBConstraintSolveBeforeStmt extends SVDBStmt {
	private List<SVExpr>				fSolveBeforeList;
	private List<SVExpr>				fSolveAfterList;
	
	public SVDBConstraintSolveBeforeStmt() {
		super(SVDBItemType.ConstraintSolveBeforeStmt);
		fSolveBeforeList = new ArrayList<SVExpr>();
		fSolveAfterList = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getSolveBeforeList() {
		return fSolveBeforeList;
	}
	
	public void addSolveBefore(SVExpr expr) {
		fSolveBeforeList.add(expr);
	}
	
	public List<SVExpr> getSolveAfterList() {
		return fSolveAfterList;
	}
	
	public void addSolveAfter(SVExpr expr) {
		fSolveAfterList.add(expr);
	}
	
	public SVDBConstraintSolveBeforeStmt duplicate() {
		SVDBConstraintSolveBeforeStmt ret = new SVDBConstraintSolveBeforeStmt();
		
		ret.fSolveBeforeList.addAll(fSolveAfterList);
		ret.fSolveAfterList.addAll(fSolveAfterList);
		
		return ret;
	}

}
