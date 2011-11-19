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

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBStmt extends SVDBChildItem {
	
	protected SVDBStmt(SVDBItemType type) {
		super(type);
	}
	
	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
	}

	@Override
	public boolean equals(Object obj) {
		return super.equals(obj);
	}
	
	@Override
	public SVDBStmt duplicate() {
		return (SVDBStmt)super.duplicate();
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		// TODO Auto-generated method stub
		return super.equals(obj, full);
	}
	
	public static boolean isType(ISVDBItemBase item, SVDBItemType ... types) {
		// TODO: item.itemClass() == SVDBItemClass.Stmt
		boolean ret = true;
		
		if (ret) {
			ret = false;
			for (SVDBItemType t : types) {
				if (t == item.getType()) {
					ret = true;
					break;
				}
			}
		}
		
		return ret;
	}
	
}
