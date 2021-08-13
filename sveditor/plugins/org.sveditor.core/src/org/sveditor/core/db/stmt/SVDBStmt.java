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

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBChildItem;
import org.sveditor.core.db.SVDBItemType;

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
