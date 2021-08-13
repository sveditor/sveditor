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


package org.sveditor.core.db;

import org.sveditor.core.db.expr.SVDBExpr;

public class SVDBParamValueAssign extends SVDBItem {
	public SVDBExpr					fValue;
	public SVDBTypeInfo				fType;

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
