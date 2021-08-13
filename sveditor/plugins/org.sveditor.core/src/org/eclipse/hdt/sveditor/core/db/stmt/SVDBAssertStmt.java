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

public class SVDBAssertStmt extends SVDBStmt {
	public SVDBExpr				fExpr;
	public SVDBExpr				fDelay;
	public SVDBActionBlockStmt		fActionBlock;
	public String				fName;
	
	public SVDBAssertStmt() {
		this(SVDBItemType.AssertStmt);
	}
	
	protected SVDBAssertStmt(SVDBItemType type) {
		super(type);
	}
	
	public void setDelay(SVDBExpr delay) {
		fDelay = delay;
	}
	
	public SVDBExpr getDelay() {
		return fDelay;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setActionBlock(SVDBActionBlockStmt stmt) {
		fActionBlock = stmt;
	}
	
	public SVDBActionBlockStmt getActionBlock() {
		return fActionBlock;
	}

	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	

}
