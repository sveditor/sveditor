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

public class SVTFCallExpr extends SVExpr {
	private SVExpr				fTarget;
	private String				fName;
	private SVExpr				fArgs[];

	public SVTFCallExpr(SVExpr target, String id, SVExpr args[]) {
		super(SVExprType.TFCall);

		fTarget = target;
		fName	= id;
		fArgs   = args;
	}
	
	public SVExpr getTarget() {
		return fTarget;
	}
	
	public String getName() {
		return fName;
	}
	
	public SVExpr [] getArgs() {
		return fArgs;
	}
	
}
