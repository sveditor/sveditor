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


package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

public class SVSolveBeforeExpr extends SVConstraintExpr {
	private List<String>				fSolveBeforeList;
	private List<String>				fSolveAfterList;
	
	public SVSolveBeforeExpr() {
		super(SVExprType.SolveBefore);
		fSolveBeforeList = new ArrayList<String>();
		fSolveAfterList = new ArrayList<String>();
	}
	
	public List<String> getSolveBeforeList() {
		return fSolveBeforeList;
	}
	
	public List<String> getSolveAfterList() {
		return fSolveAfterList;
	}
	
	public SVSolveBeforeExpr duplicate() {
		SVSolveBeforeExpr ret = new SVSolveBeforeExpr();
		
		ret.fSolveBeforeList.addAll(fSolveAfterList);
		ret.fSolveAfterList.addAll(fSolveAfterList);
		
		return ret;
	}

}
