/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.expr;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBClockedPropertyExpr extends SVDBExpr {
	public SVDBClockingEventExpr		fClockingExpr;
	public SVDBExpr						fPropertyExpr;
	
	public SVDBClockedPropertyExpr() {
		super(SVDBItemType.ClockedPropertyExpr);
	}
	
	public void setClockingExpr(SVDBClockingEventExpr expr) {
		fClockingExpr = expr;
	}
	
	public void setPropertyExpr(SVDBExpr expr) {
		fPropertyExpr = expr;
	}
	

}
