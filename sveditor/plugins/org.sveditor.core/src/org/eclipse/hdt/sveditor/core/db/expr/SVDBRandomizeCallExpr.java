/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.db.expr;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBStmt;

public class SVDBRandomizeCallExpr extends SVDBTFCallExpr {
	public SVDBStmt				fWithBlock;
	
	public SVDBRandomizeCallExpr() {
		this(null, null, null);
	}
	public SVDBRandomizeCallExpr(SVDBExpr target, String name, List<SVDBExpr> args) {
		super(SVDBItemType.RandomizeCallExpr, target, name, args);
	}
	
	public void setWithBlock(SVDBStmt with) {
		fWithBlock = with;
	}
	
	public SVDBStmt getWithBlock() {
		return fWithBlock;
	}
	
}
