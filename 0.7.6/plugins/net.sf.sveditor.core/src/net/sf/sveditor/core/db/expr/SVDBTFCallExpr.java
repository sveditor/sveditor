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

import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;


public class SVDBTFCallExpr extends SVDBExpr {
	private SVDBExpr				fTarget;
	private String					fName;
	private List<SVDBExpr>			fArgs;
	private SVDBExpr				fWithExpr;

	public SVDBTFCallExpr() {
		this(null, null, null);
	}
	
	public SVDBTFCallExpr(SVDBExpr target, String name, List<SVDBExpr> args) {
		this(SVDBItemType.TFCallExpr, target, name, args);
	}

	public SVDBTFCallExpr(SVDBItemType type, SVDBExpr target, String name, List<SVDBExpr> args) {
		super(type);

		fTarget = target;
		fName   = name;
		fArgs   = args;
	}
	
	public SVDBExpr getTarget() {
		return fTarget;
	}
	
	public String getName() {
		return fName;
	}
	
	public List<SVDBExpr> getArgs() {
		return fArgs;
	}
	
	public SVDBExpr getWithExpr() {
		return fWithExpr;
	}
	
	public void setWithExpr(SVDBExpr with) {
		fWithExpr = with;
	}
	
	public SVDBTFCallExpr duplicate() {
		return (SVDBTFCallExpr)super.duplicate();
	}
}
