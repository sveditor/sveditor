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

public class SVDBAssociativeArrayElemAssignExpr extends SVDBExpr {
	public SVDBExpr				fKey;
	public SVDBExpr				fValue;
	
	public SVDBAssociativeArrayElemAssignExpr() {
		super(SVDBItemType.AssociativeArrayElemAssignExpr);
	}
	
	public void setKey(SVDBExpr key) {
		fKey = key;
	}
	
	public SVDBExpr getKey() {
		return fKey;
	}
	
	public void setValue(SVDBExpr val) {
		fValue = val;
	}
	
	public SVDBExpr getValue() {
		return fValue;
	}

}
