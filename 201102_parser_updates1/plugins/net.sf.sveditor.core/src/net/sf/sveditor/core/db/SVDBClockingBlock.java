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


public class SVDBClockingBlock extends SVDBScopeItem {

	public SVDBClockingBlock() {
		super("", SVDBItemType.ClockingBlock);
	}
	
	public SVDBClockingBlock(String name) {
		super(name, SVDBItemType.ClockingBlock);
	}
	
	@Override
	public SVDBItemBase duplicate() {
		SVDBClockingBlock ret = new SVDBClockingBlock(getName());
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
	}

}
