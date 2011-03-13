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


public class SVDBQualifiedSuperFieldRefExpr extends SVDBExpr {
	
	private SVDBExpr				fLhs;
	private String				fId;
	
	public SVDBQualifiedSuperFieldRefExpr() {
		this(null, null);
	}
	
	public SVDBQualifiedSuperFieldRefExpr(SVDBExpr lhs, String id) {
		super(SVDBItemType.QualifiedSuperFieldRefExpr);
		
		fLhs = lhs;
		fId  = id;
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public String getId() {
		return fId;
	}
	
	public SVDBQualifiedSuperFieldRefExpr duplicate() {
		return new SVDBQualifiedSuperFieldRefExpr((SVDBExpr)fLhs.duplicate(), fId);
	}

}
