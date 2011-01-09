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

import net.sf.sveditor.core.db.SVDBItemBase;

public class SVAssignmentPatternExpr extends SVExpr {
	private List<SVExpr>			fPatternList;
	
	public SVAssignmentPatternExpr() {
		super(SVExprType.AssignmentPattern);
		fPatternList = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getPatternList() {
		return fPatternList;
	}
	
	public SVAssignmentPatternExpr duplicate() {
		SVAssignmentPatternExpr ret = new SVAssignmentPatternExpr();
		for (SVExpr e : fPatternList) {
			ret.fPatternList.add((SVExpr)e.duplicate());
		}
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		
	}

}
