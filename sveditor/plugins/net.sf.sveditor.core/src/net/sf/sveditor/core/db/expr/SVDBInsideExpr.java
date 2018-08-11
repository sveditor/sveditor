/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

public class SVDBInsideExpr extends SVDBExpr {
	public SVDBExpr					fLhs;
	public List<SVDBExpr>				fValueRangeList;
	
	public SVDBInsideExpr() {
		this(null);
	}
	
	public SVDBInsideExpr(SVDBExpr lhs) {
		super(SVDBItemType.InsideExpr);
		fLhs = lhs;
		fValueRangeList = new ArrayList<SVDBExpr>();
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public List<SVDBExpr> getValueRangeList() {
		return fValueRangeList;
	}
	
	public SVDBInsideExpr duplicate() {
		return (SVDBInsideExpr)super.duplicate();
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_inside_expr(this);
	}
	
}
