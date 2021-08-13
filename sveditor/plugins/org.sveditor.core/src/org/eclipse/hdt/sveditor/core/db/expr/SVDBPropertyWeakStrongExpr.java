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

}
