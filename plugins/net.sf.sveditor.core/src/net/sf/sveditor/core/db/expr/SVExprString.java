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

import net.sf.sveditor.core.db.SVDBItemBase;

public class SVExprString extends SVExpr {
	private String				fExprStr;
	
	public SVExprString(String expr) {
		super(SVExprType.ExprString);
		fExprStr = expr;
	}
	
	@Override
	public String toString() {
		return fExprStr;
	}

	@Override
	public SVExprString duplicate() {
		SVExprString ret = new SVExprString(fExprStr);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		SVExprString o = (SVExprString)other;
		fExprStr = o.fExprStr;
	}
}
