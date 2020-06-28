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


/**
 * @author ballance
 *
 */
public class SVDBIdentifierExpr extends SVDBExpr {
	public String					fId;
	
	public SVDBIdentifierExpr() {
		this((String)null);
	}
	
	public SVDBIdentifierExpr(String id) {
		super(SVDBItemType.IdentifierExpr);
		
		fId = id;
	}

	public SVDBIdentifierExpr(SVDBItemType type, String id) {
		super(type);
		
		fId = id;
	}

	public String getId() {
		return fId;
	}
	
	public SVDBIdentifierExpr duplicate() {
		return (SVDBIdentifierExpr)super.duplicate();
	}
	

}
