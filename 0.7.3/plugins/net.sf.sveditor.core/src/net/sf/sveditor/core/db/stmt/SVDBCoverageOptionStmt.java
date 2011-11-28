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

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCoverageOptionStmt extends SVDBStmt implements ISVDBNamedItem {
	private boolean				fIsTypeOption;
	private String				fName;
	private SVDBExpr			fExpr;
	
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
