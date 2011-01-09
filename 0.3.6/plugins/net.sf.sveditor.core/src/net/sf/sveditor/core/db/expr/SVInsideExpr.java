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

public class SVInsideExpr extends SVExpr {
	private SVExpr					fLhs;
	private List<SVExpr>			fValueRangeList;
	
	public SVInsideExpr(SVExpr lhs) {
		super(SVExprType.Inside);
		fLhs = lhs;
		fValueRangeList = new ArrayList<SVExpr>();
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public List<SVExpr> getValueRangeList() {
		return fValueRangeList;
	}
	
	public SVDBItemBase duplicate() {
		SVInsideExpr ret = new SVInsideExpr((SVExpr)fLhs.duplicate());
		
		for (SVExpr e : fValueRangeList) {
			ret.getValueRangeList().add((SVExpr)e.duplicate());
		}
		
		return ret;
	}

}
