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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBProceduralContAssignStmt extends SVDBStmt {
	public enum AssignType {
		Assign,
		Deassign,
		Force,
		Release
	};
	
	private AssignType				fAssignType;
	private SVDBExpr					fExpr;
	
	public SVDBProceduralContAssignStmt() {
		super(SVDBItemType.ProceduralContAssignStmt);
	}
	
	public SVDBProceduralContAssignStmt(AssignType type) {
		super(SVDBItemType.ProceduralContAssignStmt);
		fAssignType = type;
	}
	
	public AssignType getAssignType() {
		return fAssignType;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
