/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBPropertyWeakStrongExpr extends SVDBExpr {
	public boolean				fIsWeak;
	public SVDBExpr			fExpr;
	
	
	public SVDBPropertyWeakStrongExpr() {
		super(SVDBItemType.PropertyWeakStrongExpr);
	}
	
	public void setIsWeak(boolean is_weak) {
		fIsWeak = is_weak;
	}
	
	public boolean getIsWeak() {
		return fIsWeak;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_property_weak_strong_expr(this);
	}
}
