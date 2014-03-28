/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
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
