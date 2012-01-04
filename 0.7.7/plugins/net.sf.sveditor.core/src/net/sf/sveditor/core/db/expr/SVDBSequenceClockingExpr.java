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

public class SVDBSequenceClockingExpr extends SVDBExpr {
	SVDBExpr 		fClockingExpr;
	SVDBExpr		fSequenceExpr;
	
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
