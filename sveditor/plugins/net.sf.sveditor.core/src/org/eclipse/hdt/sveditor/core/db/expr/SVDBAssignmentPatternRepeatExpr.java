/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

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
