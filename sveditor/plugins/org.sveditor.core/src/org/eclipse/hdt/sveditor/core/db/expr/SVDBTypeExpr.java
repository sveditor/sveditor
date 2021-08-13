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


package org.eclipse.hdt.sveditor.core.db.expr;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;

public class SVDBTypeExpr extends SVDBExpr {
	public SVDBTypeInfo			fTypeInfo;
	
	public SVDBTypeExpr() {
		super(SVDBItemType.TypeExpr);
	}
	
	public SVDBTypeExpr(SVDBTypeInfo type) {
		this();
		fTypeInfo = type;
	}
	
	public void setTypeInfo(SVDBTypeInfo type) {
		fTypeInfo = type;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fTypeInfo;
	}

}
