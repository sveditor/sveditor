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

public class SVLiteralExpr extends SVExpr {
	
	private String					fLiteral;
	
	public SVLiteralExpr(String literal) {
		super(SVExprType.Literal);
		
		fLiteral = literal;
	}
	
	public String getValue() {
		return fLiteral;
	}
	
	public SVDBItemBase duplicate() {
		return new SVLiteralExpr(fLiteral);
	}

}
