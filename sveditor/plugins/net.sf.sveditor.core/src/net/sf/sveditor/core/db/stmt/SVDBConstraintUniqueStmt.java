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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBOpenRangeListExpr;

public class SVDBConstraintUniqueStmt extends SVDBStmt {
	public SVDBOpenRangeListExpr				fExpr;
	
	public SVDBConstraintUniqueStmt() {
		super(SVDBItemType.ConstraintUniqueStmt);
	}
	
	public void setExpr(SVDBOpenRangeListExpr expr) {
		fExpr = expr;
	}
	
	public SVDBOpenRangeListExpr getExpr() {
		return fExpr;
	}
	
}
