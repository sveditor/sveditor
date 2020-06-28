/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBAlias extends SVDBStmt {
	public SVDBExpr				fLvalue;
	public List<SVDBExpr>		fAliases;
	
	public SVDBAlias() {
		super(SVDBItemType.Alias);
		fAliases = new ArrayList<SVDBExpr>();
	}
	
	public void setLvalue(SVDBExpr expr) {
		fLvalue = expr;
	}
	
	public void addAlias(SVDBExpr expr) {
		fAliases.add(expr);
	}

}
