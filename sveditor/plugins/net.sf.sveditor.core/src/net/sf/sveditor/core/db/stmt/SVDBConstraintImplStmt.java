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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;


public class SVDBConstraintImplStmt extends SVDBStmt {
	
	public SVDBExpr					fExpr;
	public SVDBStmt				fConstraint;
	
	public SVDBConstraintImplStmt() {
		super(SVDBItemType.ConstraintImplStmt);
	}
	
	public SVDBConstraintImplStmt(SVDBExpr expr, SVDBStmt constraint) {
		super(SVDBItemType.ConstraintImplStmt);
		fExpr 		= expr;
		fConstraint = constraint;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public SVDBStmt getConstraintSet() {
		return fConstraint;
	}
	
	public SVDBConstraintImplStmt duplicate() {
		return (SVDBConstraintImplStmt)super.duplicate();
	}

}
