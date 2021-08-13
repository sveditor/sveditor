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


package org.sveditor.core.db.stmt;

import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.expr.SVDBExpr;

public class SVDBEventTriggerStmt extends SVDBStmt {
	public SVDBStmt			fDelayOrEventControl;
	public SVDBExpr				fHierarchicalEventIdentifier;
	
	public SVDBEventTriggerStmt() {
		super(SVDBItemType.EventTriggerStmt);
	}
	
	public SVDBStmt getDelayOrEventControl() {
		return fDelayOrEventControl;
	}
	
	public void setDelayOrEventControl(SVDBStmt stmt) {
		fDelayOrEventControl = stmt;
	}
	
	public SVDBExpr getHierarchicalEventIdentifier() {
		return fHierarchicalEventIdentifier;
	}
	
	public void setHierarchicalEventIdentifier(SVDBExpr expr) {
		fHierarchicalEventIdentifier = expr;
	}

}
