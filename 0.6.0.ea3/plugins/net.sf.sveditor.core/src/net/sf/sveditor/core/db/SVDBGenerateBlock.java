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


public class SVDBGenerateBlock extends SVDBScopeItem {

	public SVDBGenerateBlock() {
		super("", SVDBItemType.GenerateBlock);
	}
	
	public SVDBGenerateBlock(String name) {
		super(name, SVDBItemType.GenerateBlock);
	}
	
	@Override
	public void init(SVDBItemBase other) {
		// TODO Auto-generated method stub
		super.init(other);
	}

	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBGenerateBlock) {
			return super.equals(obj);
		} else {
			return false;
		}
	}
	 */

}
