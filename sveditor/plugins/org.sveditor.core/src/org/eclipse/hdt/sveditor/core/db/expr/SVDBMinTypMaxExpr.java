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
package org.eclipse.hdt.sveditor.core.db.expr;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBMinTypMaxExpr extends SVDBExpr {
	public SVDBExpr			fMin;
	public SVDBExpr			fTyp;
	public SVDBExpr			fMax;
	
	public SVDBMinTypMaxExpr() {
		super(SVDBItemType.MinTypMaxExpr);
	}

	public SVDBMinTypMaxExpr(SVDBExpr min, SVDBExpr typ, SVDBExpr max) {
		this();
		fMin = min;
		fTyp = typ;
		fMax = max;
	}
}
