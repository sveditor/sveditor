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

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBStringExpr extends SVDBExpr {
	public String				fStr;
	
	public SVDBStringExpr() {
		this("");
	}
	
	public SVDBStringExpr(String str) {
		super(SVDBItemType.StringExpr);
		fStr = str;
	}
	
	public String getContent() {
		return fStr;
	}
	
	public SVDBStringExpr duplicate() {
		return (SVDBStringExpr)super.duplicate();
	}

}
