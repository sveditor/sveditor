/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;


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
