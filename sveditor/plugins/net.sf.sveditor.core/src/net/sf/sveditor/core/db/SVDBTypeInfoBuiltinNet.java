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


public class SVDBTypeInfoBuiltinNet extends SVDBTypeInfo {
	
	public String					fWireType;
	public SVDBTypeInfo				fType;
	
	public SVDBTypeInfoBuiltinNet() {
		this("", null);
	}
	
	public SVDBTypeInfoBuiltinNet(String wire_type, SVDBTypeInfo type) {
		super(wire_type, SVDBItemType.TypeInfoBuiltinNet);
		fWireType = wire_type;
		fType     = type;
	}
	
	public String getWireType() {
		return fWireType;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fType;
	}
	
	public String toString() {
		String ret;
		
		if (fType != null) {
			ret = fType.toString();
		} else {
			ret = super.toString();
		}
		
		return ret;
	}
}
