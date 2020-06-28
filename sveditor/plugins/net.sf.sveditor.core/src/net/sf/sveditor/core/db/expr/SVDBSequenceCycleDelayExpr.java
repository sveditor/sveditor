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


package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBSequenceCycleDelayExpr extends SVDBExpr {
	public SVDBExpr				fLhs;
	public SVDBCycleDelayExpr		fDelay;
	public SVDBExpr				fRhs;
	
	public SVDBSequenceCycleDelayExpr() {
		super(SVDBItemType.SequenceCycleDelayExpr);
	}
	
	public void setDelay(SVDBCycleDelayExpr expr) {
		fDelay = expr;
	}
	
	public SVDBCycleDelayExpr getDelay() {
		return fDelay;
	}
	
	public void setLhs(SVDBExpr expr) {
		fLhs = expr;
	}
	
	public SVDBExpr getLhs() {
		return fLhs;
	}
	
	public void setRhs(SVDBExpr expr) {
		fRhs = expr;
	}
	
	public SVDBExpr getRhs() {
		return fRhs;
	}

}
