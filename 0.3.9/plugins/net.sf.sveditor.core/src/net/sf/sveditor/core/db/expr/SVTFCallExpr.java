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


public class SVTFCallExpr extends SVExpr {
	private SVExpr				fTarget;
	private String				fName;
	private SVExpr				fArgs[];

	public SVTFCallExpr(SVExpr target, String name, SVExpr args[]) {
		super(SVExprType.TFCall);

		fTarget = target;
		fName   = name;
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
	
	public SVTFCallExpr duplicate() {
		SVExpr args[] = new SVExpr[fArgs.length];
		
		for (int i=0; i<fArgs.length; i++) {
			args[i] = (SVExpr)fArgs[i].duplicate();
		}
		
		return new SVTFCallExpr((SVExpr)fTarget.duplicate(), fName, args);
	}
}
