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


package org.sveditor.core.db;

import org.sveditor.core.db.expr.SVDBExpr;


public class SVDBClockingBlock extends SVDBScopeItem {
	public SVDBExpr				fExpr;

	public SVDBClockingBlock() {
		super("", SVDBItemType.ClockingBlock);
	}
	
	public SVDBClockingBlock(String name) {
		super(name, SVDBItemType.ClockingBlock);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	@Override
	public SVDBClockingBlock duplicate() {
		return (SVDBClockingBlock)SVDBItemUtils.duplicate(this);
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
	}

}
