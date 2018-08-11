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

import net.sf.sveditor.core.db.ISVDBVisitor;
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

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_sequence_cycle_delay_expr(this);
	}
}
