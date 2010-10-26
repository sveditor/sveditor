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

public class SVIdentifierExpr extends SVExpr {
	private String				fId[];
	private String				fIdStr;
	
	public SVIdentifierExpr(String ... id) {
		super(SVExprType.Identifier);
		
		fId = id;
	}
	
	public String[] getId() {
		return fId;
	}
	
	public String getIdStr() {
		if (fIdStr == null) {
			StringBuilder builder = new StringBuilder();
			for (int i=0; i<fId.length; i++) {
				builder.append(fId[i]);
				if (i+1 < fId.length) {
					builder.append(".");
				}
			}
			fIdStr = builder.toString();
		}
		
		return fIdStr;
	}
	
	public SVExpr duplicate() {
		return new SVIdentifierExpr(fId);
	}
	

}
