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
package org.eclipse.hdt.sveditor.core.db.stmt;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigCellClauseStmt extends SVDBConfigRuleStmtBase {
	
	public SVDBExpr					fCellId;
	
	public SVDBConfigCellClauseStmt() {
		super(SVDBItemType.ConfigCellClauseStmt);
	}
	
	public void setCellId(SVDBExpr id) {
		fCellId = id;
	}

}
