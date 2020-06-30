/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db;

import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBTypeInfoEnumerator extends SVDBTypeInfo {
	public SVDBExpr				fExpr;
	
	public SVDBTypeInfoEnumerator() {
		this("");
	}
	
	public SVDBTypeInfoEnumerator(String name) {
		super(name, SVDBItemType.TypeInfoEnumerator);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}

	public SVDBExpr getExpr() {
		return fExpr;
	}
}
