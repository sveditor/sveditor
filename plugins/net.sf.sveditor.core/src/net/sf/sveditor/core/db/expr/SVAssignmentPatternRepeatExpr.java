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

public class SVAssignmentPatternRepeatExpr extends SVAssignmentPatternExpr {
	private SVExpr					fRepeatExpr;
	
	public SVAssignmentPatternRepeatExpr(SVExpr repeat_expr) {
		super();
		fRepeatExpr = repeat_expr;
	}

	public SVExpr getRepeatExpr() {
		return fRepeatExpr;
	}
}
