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

public class SVDBParamValueAssign extends SVDBItem {
	SVDBExpr					fValue;
	SVDBTypeInfo				fType;

	public SVDBParamValueAssign() {
		super("", SVDBItemType.ParamValueAssign);
	}
	
	public SVDBParamValueAssign(String name, SVDBExpr value) {
		super(name, SVDBItemType.ParamValueAssign);
		fValue = value;
	}

	public SVDBParamValueAssign(String name, SVDBTypeInfo type) {
		super(name, SVDBItemType.ParamValueAssign);
		fType = type;
	}

	public SVDBExpr getValue() {
		return fValue;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fType;
	}

}
