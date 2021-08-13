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

public class SVDBSequenceMatchItemExpr extends SVDBExpr {
	public SVDBExpr			fExpr;
	public List<SVDBExpr>		fMatchItemList;
	public SVDBExpr			fSequenceAbbrev;
	
	public SVDBSequenceMatchItemExpr() {
		super(SVDBItemType.SequenceMatchItemExpr);
		fMatchItemList = new ArrayList<SVDBExpr>();
	}

	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void addMatchItemExpr(SVDBExpr expr) {
		fMatchItemList.add(expr);
	}
	
	public List<SVDBExpr> getMatchItemExprList() {
		return fMatchItemList;
	}
	
	public void setSequenceAbbrev(SVDBExpr expr) {
		fSequenceAbbrev = expr;
	}
	
	public SVDBExpr getSequenceAbbrev() {
		return fSequenceAbbrev;
	}
}
