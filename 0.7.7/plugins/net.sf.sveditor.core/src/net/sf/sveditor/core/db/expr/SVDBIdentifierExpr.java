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

import net.sf.sveditor.core.db.SVDBItemType;


/**
 * @author ballance
 *
 */
public class SVDBIdentifierExpr extends SVDBExpr {
	String					fId;
	
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
