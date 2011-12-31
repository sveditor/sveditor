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

public class SVDBEventTriggerStmt extends SVDBStmt {
	private SVDBStmt			fDelayOrEventControl;
	private SVDBExpr				fHierarchicalEventIdentifier;
	
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
