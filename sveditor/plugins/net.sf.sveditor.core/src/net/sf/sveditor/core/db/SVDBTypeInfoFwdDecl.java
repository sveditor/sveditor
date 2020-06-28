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


public class SVDBTypeInfoFwdDecl extends SVDBTypeInfo {
	
	public String					fTypeClass; // class, enum, union, struct
	
	public SVDBTypeInfoFwdDecl() {
		this("", "");
	}
	
	public SVDBTypeInfoFwdDecl(String type_class, String typename) {
		super(typename, SVDBItemType.TypeInfoFwdDecl);
		fTypeClass = type_class;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoFwdDecl) {
			SVDBTypeInfoFwdDecl o = (SVDBTypeInfoFwdDecl)obj;
			
			return (fTypeClass.equals(o.fTypeClass) &&
					super.equals(obj));
		}
		return false;
	}

	@Override
	public SVDBTypeInfoFwdDecl duplicate() {
		return (SVDBTypeInfoFwdDecl)super.duplicate(); 
	}
	
}
