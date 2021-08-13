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


package org.eclipse.hdt.sveditor.core.db;

import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBModIfcClassParam extends SVDBItem {
	
	public SVDBExpr					fDefault;
	public SVDBTypeInfo				fDefaultType;
	
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
	
	public SVDBModIfcClassParam duplicate() {
		return (SVDBModIfcClassParam)super.duplicate();
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
