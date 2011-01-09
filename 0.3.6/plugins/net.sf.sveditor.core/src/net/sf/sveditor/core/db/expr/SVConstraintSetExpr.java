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

public class SVConstraintSetExpr extends SVExpr {
	private List<SVExpr>				fConstraintList;
	
	public SVConstraintSetExpr() {
		super(SVExprType.ConstraintSet);
		fConstraintList = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getConstraintList() {
		return fConstraintList;
	}
	
	public SVDBItemBase duplicate() {
		SVConstraintSetExpr ret = new SVConstraintSetExpr();
		
		for (SVExpr e : fConstraintList) {
			ret.fConstraintList.add((SVExpr)e.duplicate());
		}
		
		return ret;
	}

}
