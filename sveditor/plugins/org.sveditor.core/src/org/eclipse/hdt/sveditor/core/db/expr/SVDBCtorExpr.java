/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBCtorExpr extends SVDBExpr {
	public enum CtorType {
		CtorType_Args,
		CtorType_Dim,
		CtorType_Expr,
		CtorType_Void
	}
	public CtorType					fCtorType = CtorType.CtorType_Void;
	public List<SVDBExpr>			fArgs;
	
	public SVDBCtorExpr() {
		super(SVDBItemType.CtorExpr);
	}
	
	public void setCtorType(CtorType type) {
		fCtorType = type;
	}
	
	public CtorType getCtorType() {
		return fCtorType;
	}
	
	public void setArg(SVDBExpr expr) {
		if (fArgs == null) {
			fArgs = new ArrayList<SVDBExpr>();
		}
		fArgs.clear();
		fArgs.add(expr);
	}

	public SVDBExpr getArg() {
		if (fArgs == null || fArgs.size() == 0) {
			return null;
		} else {
			return fArgs.get(0);
		}
	}

	public void setArgs(List<SVDBExpr> args) {
		fArgs = args;
	}
	
	public List<SVDBExpr> getArgs() {
		return fArgs;
	}
	
}
