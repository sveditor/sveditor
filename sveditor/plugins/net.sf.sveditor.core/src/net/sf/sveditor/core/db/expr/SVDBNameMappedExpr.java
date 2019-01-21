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

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBNameMappedExpr extends SVDBExpr {
	public SVDBExpr			fName;
	public SVDBExpr			fExpr;
	
	public SVDBNameMappedExpr() {
		super(SVDBItemType.NameMappedExpr);
	}
	
	public SVDBNameMappedExpr(String name, SVDBExpr expr) {
		this();
		fName = new SVDBLiteralExpr(name);
		fExpr = expr;
	}
	
	public SVDBNameMappedExpr(SVDBExpr name, SVDBExpr expr) {
		this();
		fName = name;
		fExpr = expr;
	}
	
	public SVDBExpr getName() {
		return fName;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_name_mapped_expr(this);
	}
	
}
