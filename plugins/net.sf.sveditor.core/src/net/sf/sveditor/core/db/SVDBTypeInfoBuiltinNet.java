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


public class SVDBTypeInfoBuiltinNet extends SVDBTypeInfo {
	
	public String					fWireType;
	public SVDBTypeInfo			fType;
	
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
}
