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
