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


package net.sf.sveditor.core.expr.parser;

public class SVQualifiedSuperFieldRefExpr extends SVExpr {
	
	private SVExpr				fLhs;
	private String				fId;
	
	public SVQualifiedSuperFieldRefExpr(SVExpr lhs, String id) {
		super(SVExprType.QualifiedSuperFieldRef);
		
		fLhs = lhs;
		fId  = id;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public String getId() {
		return fId;
	}

}
