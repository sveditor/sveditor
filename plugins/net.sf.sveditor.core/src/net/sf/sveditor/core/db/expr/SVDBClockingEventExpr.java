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

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBClockingEventExpr extends SVDBExpr {
	public enum ClockingEventType {
		None, // always ... 
		Any,  // @(*)
		Expr // always @(a or b or c)
	}

	SVDBExpr			fExpr;
	ClockingEventType   fEventType;


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
