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

import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBCoverageOptionStmt extends SVDBStmt implements ISVDBNamedItem {
	public boolean				fIsTypeOption;
	public String				fName;
	public SVDBExpr			fExpr;
	
	public SVDBCoverageOptionStmt() {
		super(SVDBItemType.CoverageOptionStmt);
	}
	
	public SVDBCoverageOptionStmt(String name, boolean is_type_option) {
		super(SVDBItemType.CoverageOptionStmt);
		fName = name;
		fIsTypeOption = is_type_option;
	}
	
	public boolean isTypeOption() {
		return fIsTypeOption;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	

}
