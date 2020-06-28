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

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBPropertySpecExpr extends SVDBExpr {
	public SVDBClockingEventExpr			fClockingEventExpr;
	public SVDBExpr						fDisableExpr;
	public SVDBExpr						fExpr;
	
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
