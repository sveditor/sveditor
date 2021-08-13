/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.SVDBItemType;

public class SVDBCrossBinsSelectConditionExpr extends SVDBExpr {
	public SVDBExpr					fBinsExpr;
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
