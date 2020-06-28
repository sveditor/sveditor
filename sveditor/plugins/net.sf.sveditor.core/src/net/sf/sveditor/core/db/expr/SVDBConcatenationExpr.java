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


package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBConcatenationExpr extends SVDBExpr {
	public List<SVDBExpr>			fElems;
	
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
