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

public class SVDBModIfcClassParam extends SVDBItem {
	
	private SVDBExpr					fDefault;
	private SVDBTypeInfo			fDefaultType;
	
	public SVDBModIfcClassParam() {
		super("", SVDBItemType.ModIfcClassParam);
	}

	public SVDBModIfcClassParam(String name) {
		super(name, SVDBItemType.ModIfcClassParam);
	}
	
	public SVDBExpr getDefault() {
		return fDefault;
	}
	
	public void setDefault(SVDBExpr dflt) {
		fDefault = dflt;
	}
	
	public SVDBTypeInfo getDefaultType() {
		return fDefaultType;
	}
	
	public void setDefaultType(SVDBTypeInfo type) {
		fDefaultType = type;
	}
	
	public SVDBItemBase duplicate() {
		SVDBItem ret = new SVDBModIfcClassParam(getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		fDefault = ((SVDBModIfcClassParam)other).fDefault;
	}

	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBModIfcClassParam) {
			boolean ret = fDefault.equals(((SVDBModIfcClassParam)obj).fDefault);
			ret &= super.equals(obj);
			
			return ret;
		}
		
		return false;
	}
	 */
	
}
