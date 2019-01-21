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
import net.sf.sveditor.core.db.SVDBParamValueAssignList;

public class SVDBParamIdExpr extends SVDBIdentifierExpr {
	public SVDBParamValueAssignList		fParamExpr;
	
	public SVDBParamIdExpr() {
		this(null);
	}

	public SVDBParamIdExpr(String id) {
		super(SVDBItemType.ParamIdExpr, id);
	}

	public SVDBParamValueAssignList getParamExpr() {
		return fParamExpr;
	}
	
	public void setParamExpr(SVDBParamValueAssignList plist) {
		fParamExpr = plist;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_param_id_expr(this);
	}
	
}
