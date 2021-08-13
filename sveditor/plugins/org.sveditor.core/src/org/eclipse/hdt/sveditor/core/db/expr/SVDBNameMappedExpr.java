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


package org.sveditor.core.db.expr;

import org.sveditor.core.db.SVDBItemType;

public class SVDBNameMappedExpr extends SVDBExpr {
	public SVDBExpr			fName;
	public SVDBExpr			fExpr;
	
	public SVDBNameMappedExpr() {
		super(SVDBItemType.NameMappedExpr);
	}
	
	public SVDBNameMappedExpr(String name, SVDBExpr expr) {
		this();
		fName = new SVDBLiteralExpr(name);
		fExpr = expr;
	}
	
	public SVDBNameMappedExpr(SVDBExpr name, SVDBExpr expr) {
		this();
		fName = name;
		fExpr = expr;
	}
	
	public SVDBExpr getName() {
		return fName;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
