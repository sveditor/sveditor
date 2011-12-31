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

public class SVDBPropertySpecExpr extends SVDBExpr {
	private SVDBClockingEventExpr			fClockingEventExpr;
	private SVDBExpr						fDisableExpr;
	private SVDBExpr						fExpr;
	
	public SVDBPropertySpecExpr() {
		super(SVDBItemType.PropertySpecExpr);
	}

	public SVDBClockingEventExpr getClockingEvent() {
		return fClockingEventExpr;
	}
	
	public void setClockingEvent(SVDBClockingEventExpr expr) {
		fClockingEventExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getDisableExpr() {
		return fDisableExpr;
	}
	
	public void setDisableExpr(SVDBExpr expr) {
		fDisableExpr = expr;
	}
}
