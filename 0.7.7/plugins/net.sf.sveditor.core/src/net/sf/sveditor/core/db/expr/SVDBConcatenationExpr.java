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
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBConcatenationExpr extends SVDBExpr {
	List<SVDBExpr>			fElems;
	
	public SVDBConcatenationExpr() {
		super(SVDBItemType.ConcatenationExpr);
		fElems = new ArrayList<SVDBExpr>();
	}
	
	public List<SVDBExpr> getElements() {
		return fElems;
	}
	
	public SVDBConcatenationExpr duplicate() {
		return (SVDBConcatenationExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		SVDBConcatenationExpr ce = (SVDBConcatenationExpr)other;
		
		super.init(other);
		
		fElems.clear();
		
		for (SVDBExpr e : ce.fElems) {
			fElems.add((SVDBExpr)e.duplicate());
		}
	}
	

}
