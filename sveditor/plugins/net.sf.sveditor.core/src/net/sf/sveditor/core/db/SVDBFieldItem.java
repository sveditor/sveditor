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


package net.sf.sveditor.core.db;


public class SVDBFieldItem extends SVDBItem implements IFieldItemAttr {
	
	public int					fFieldAttr;
	
	public SVDBFieldItem(String name, SVDBItemType type) {
		super(name, type);
		SVDBInclude inc = new SVDBInclude();
		inc.fName = "foo";
	}
	
	public int getAttr() {
		return fFieldAttr;
	}
	
	public void setAttr(int attr) {
		fFieldAttr = attr;
	}
	
	/*
	public boolean equals(Object obj) {
		if (obj instanceof SVDBFieldItem) {
			boolean ret = super.equals(obj);
			ret &= ((SVDBFieldItem)obj).fFieldAttr == fFieldAttr;
			return ret;
		}
		return false;
	}
	 */

	public void init(SVDBItemBase other) {
		super.init(other);
		
		fFieldAttr = ((SVDBFieldItem)other).fFieldAttr;
	}

}
