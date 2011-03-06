/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;


public class SVDBConstraintImplStmt extends SVDBStmt {
	
	private SVExpr					fExpr;
	private SVDBStmt				fConstraint;
	
	
	public SVDBConstraintImplStmt(SVExpr expr, SVDBStmt constraint) {
		super(SVDBItemType.ConstraintImplStmt);
		fExpr 		= expr;
		fConstraint = constraint;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public SVDBStmt getConstraintSet() {
		return fConstraint;
	}
	
	public SVDBConstraintImplStmt duplicate() {
		return new SVDBConstraintImplStmt(
				(SVExpr)fExpr.duplicate(), 
				(SVDBConstraintSetStmt)fConstraint.duplicate());
	}

}
