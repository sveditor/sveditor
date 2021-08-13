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


package org.eclipse.hdt.sveditor.core.db.stmt;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBProceduralContAssignStmt extends SVDBStmt {
	public enum AssignType {
		Assign,
		Deassign,
		Force,
		Release
	};
	
	public AssignType				fAssignType;
	public SVDBExpr					fExpr;
	
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
