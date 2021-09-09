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


package org.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.SVDBItemType;

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

}
