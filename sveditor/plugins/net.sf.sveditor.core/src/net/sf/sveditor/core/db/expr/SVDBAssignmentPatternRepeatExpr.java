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

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBAssignmentPatternRepeatExpr extends SVDBAssignmentPatternExpr {
	public SVDBExpr					fRepeatExpr;
	
	public SVDBAssignmentPatternRepeatExpr() {
		this(null);
	}
	
	public SVDBAssignmentPatternRepeatExpr(SVDBExpr repeat_expr) {
		super(SVDBItemType.AssignmentPatternRepeatExpr);
		fRepeatExpr = repeat_expr;
	}

	public void setRepeatExpr(SVDBExpr e) {
		fRepeatExpr = e;
	}
	
	public SVDBExpr getRepeatExpr() {
		return fRepeatExpr;
	}
}
