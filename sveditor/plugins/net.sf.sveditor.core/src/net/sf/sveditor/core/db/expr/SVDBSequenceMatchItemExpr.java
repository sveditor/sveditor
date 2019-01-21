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

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

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
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_sequence_match_item_expr(this);
	}
}
