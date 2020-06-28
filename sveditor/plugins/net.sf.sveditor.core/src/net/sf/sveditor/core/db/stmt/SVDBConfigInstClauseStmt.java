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
package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigInstClauseStmt extends SVDBConfigRuleStmtBase {
	
	public SVDBExpr		fInstName;
	
	public SVDBConfigInstClauseStmt() {
		super(SVDBItemType.ConfigInstClauseStmt);
	}
	
	public void setInstName(SVDBExpr inst) {
		fInstName = inst;
	}

}
