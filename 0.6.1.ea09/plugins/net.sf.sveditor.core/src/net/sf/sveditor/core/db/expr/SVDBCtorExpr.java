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

import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCtorExpr extends SVDBExpr {
	private List<SVDBExpr>			fArgs;
	private SVDBExpr				fDim;
	
	public SVDBCtorExpr() {
		super(SVDBItemType.CtorExpr);
	}
	
	public void setArgs(List<SVDBExpr> args) {
		fArgs = args;
	}
	
	public List<SVDBExpr> getArgs() {
		return fArgs;
	}
	
	public void setDim(SVDBExpr dim) {
		fDim = dim;
	}
	
	public SVDBExpr getDim() {
		return fDim;
	}

}
