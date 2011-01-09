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

public class SVConcatenationExpr extends SVExpr {
	private List<SVExpr>			fElems;
	
	public SVConcatenationExpr() {
		super(SVExprType.Concatenation);
		fElems = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getElements() {
		return fElems;
	}
	
	public SVDBItemBase duplicate() {
		SVConcatenationExpr ret = new SVConcatenationExpr();
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		SVConcatenationExpr ce = (SVConcatenationExpr)other;
		
		super.init(other);
		
		fElems.clear();
		
		for (SVExpr e : ce.fElems) {
			fElems.add((SVExpr)e.duplicate());
		}
	}
	

}
