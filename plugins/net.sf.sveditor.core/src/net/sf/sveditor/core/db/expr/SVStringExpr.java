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


package net.sf.sveditor.core.db.expr;

public class SVStringExpr extends SVExpr {
	private String				fStr;
	
	public SVStringExpr(String str) {
		super(SVExprType.String);
		fStr = str;
	}
	
	public String getContent() {
		return fStr;
	}
	
	public SVStringExpr duplicate() {
		SVStringExpr ret = new SVStringExpr(fStr);
		
		ret.init(ret);
		
		return ret;
	}

}
