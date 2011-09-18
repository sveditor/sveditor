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
