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

public class SVDBDisableStmt extends SVDBStmt {
	public SVDBExpr				fHierarchicalId;
	
	public SVDBDisableStmt() {
		this(SVDBItemType.DisableStmt);
	}
	
	protected SVDBDisableStmt(SVDBItemType type) {
		super(type);
	}
	
	public void setHierarchicalId(SVDBExpr expr) {
		fHierarchicalId = expr;
	}

	public SVDBExpr getHierarchicalId() {
		return fHierarchicalId;
	}
}
