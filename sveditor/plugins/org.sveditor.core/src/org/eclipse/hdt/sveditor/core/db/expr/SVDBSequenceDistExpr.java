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

import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.stmt.SVDBConstraintDistListStmt;

public class SVDBSequenceDistExpr extends SVDBExpr {
	public SVDBExpr					fExpr;
	public SVDBConstraintDistListStmt	fDistExpr;

	public SVDBSequenceDistExpr() {
		super(SVDBItemType.SequenceDistExpr);
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBConstraintDistListStmt getDistExpr() {
		return fDistExpr;
	}
	
	public void setDistExpr(SVDBConstraintDistListStmt dist) {
		fDistExpr = dist;
	}
}
