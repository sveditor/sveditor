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


package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBNamedArgExpr extends SVDBExpr {
	public String				fArgName;
	public SVDBExpr			fExpr;
	
	public SVDBNamedArgExpr() {
		super(SVDBItemType.NamedArgExpr);
	}
	
	public void setArgName(String name) {
		fArgName = name;
	}
	
	public String getArgName() {
		return fArgName;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
