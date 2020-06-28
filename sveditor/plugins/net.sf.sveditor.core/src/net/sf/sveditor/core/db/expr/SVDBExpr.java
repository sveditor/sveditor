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


package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBItemUtils;

public class SVDBExpr extends SVDBItemBase {
	
	protected SVDBExpr(SVDBItemType type) {
		super(type);
	}
	
	public String toString() {
		return SVExprUtils.getDefault().exprToString(this);
	}
	
	public SVDBExpr duplicate() {
		return (SVDBExpr)SVDBItemUtils.duplicate(this);
	}
	
	public void init(SVDBItemBase other) {
		SVDBExpr o = (SVDBExpr)other;
		super.init(o);
	}
}
