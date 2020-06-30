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

public class SVDBSequenceClockingExpr extends SVDBExpr {
	public SVDBExpr 		fClockingExpr;
	public SVDBExpr		fSequenceExpr;
	
	public SVDBSequenceClockingExpr() {
		super(SVDBItemType.SequenceClockingExpr);
	}
	
	public void setClockingExpr(SVDBExpr expr) {
		fClockingExpr = expr;
	}
	
	public SVDBExpr getClockingExpr() {
		return fClockingExpr;
	}
	
	public void setSequenceExpr(SVDBExpr expr) {
		fSequenceExpr = expr;
	}
	
	public SVDBExpr getSequenceExpr() {
		return fSequenceExpr;
	}

}
