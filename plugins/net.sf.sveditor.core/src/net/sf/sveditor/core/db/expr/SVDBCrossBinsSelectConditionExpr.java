/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCrossBinsSelectConditionExpr extends SVDBExpr {
	public SVDBExpr				fBinsExpr;
	public List<SVDBExpr>			fIntersectList;
	
	public SVDBCrossBinsSelectConditionExpr() {
		super(SVDBItemType.CrossBinsSelectConditionExpr);
		fIntersectList = new ArrayList<SVDBExpr>();
	}
	
	public void setBinsExpr(SVDBExpr expr) {
		fBinsExpr = expr;
	}
	
	public SVDBExpr getBinsExpr() {
		return fBinsExpr;
	}
	
	public List<SVDBExpr> getIntersectList() {
		return fIntersectList;
	}

}
