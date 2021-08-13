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


package org.sveditor.core.db.expr;

import org.sveditor.core.db.SVDBItemType;

public class SVDBClockingEventExpr extends SVDBExpr {
	public enum ClockingEventType {
		None, // always ... 
		Any,  // @(*)
		Expr // always @(a or b or c)
	}

	public SVDBExpr			fExpr;
	public ClockingEventType   fEventType;


	public SVDBClockingEventExpr() {
		super(SVDBItemType.ClockingEventExpr);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

	public void setClockingEventType(ClockingEventType type) {
		fEventType = type;
	}
	
	public ClockingEventType getClockingEventType() {
		return fEventType;
	}

}
