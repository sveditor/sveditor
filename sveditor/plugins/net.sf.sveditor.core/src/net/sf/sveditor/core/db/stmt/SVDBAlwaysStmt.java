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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr.ClockingEventType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAlwaysStmt extends SVDBBodyStmt {
	
	public enum AlwaysType {
		Always,
		AlwaysComb,
		AlwaysLatch,
		AlwaysFF
	};
	
	public AlwaysType				fAlwaysType;
	public SVDBClockingEventExpr 	fAlwaysEventExprType;
	
	public SVDBAlwaysStmt() {
		this(AlwaysType.Always);
		fAlwaysEventExprType = new SVDBClockingEventExpr();
	}
	
	public SVDBAlwaysStmt(AlwaysType type) {
		super(SVDBItemType.AlwaysStmt);
		fAlwaysType = type;
		fAlwaysEventExprType = new SVDBClockingEventExpr();
	}
	
	public AlwaysType getAlwaysType() {
		return fAlwaysType;
	}
	
	public ClockingEventType getAlwaysEventType() {
		return fAlwaysEventExprType.getClockingEventType();
	}
	
	public void setAlwaysEventType(ClockingEventType type) {
		fAlwaysEventExprType.setClockingEventType(type);
	}
	
	public SVDBExpr getEventExpr() {
		return fAlwaysEventExprType.getExpr();
	}
	
	public void setEventExpr(SVDBExpr expr) {
		fAlwaysEventExprType.setExpr(expr);
	}
	
	public SVDBClockingEventExpr getCBEventExpr() {
		return fAlwaysEventExprType;
	}
	
	public void setCBEventExpr(SVDBClockingEventExpr cbExpr) {
		fAlwaysEventExprType = cbExpr;
	}
	
	@Override
	public SVDBAlwaysStmt duplicate() {
		return (SVDBAlwaysStmt)super.duplicate();
	}

	@Override
	public void init(ISVDBItemBase other) {
		super.init(other);
		fAlwaysType = ((SVDBAlwaysStmt)other).fAlwaysType;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBAlwaysStmt) {
			boolean ret = true;
			ret &= ((SVDBAlwaysStmt)obj).fAlwaysType.equals(fAlwaysType);
			ret &= super.equals(obj);
			
			return ret;
		}
		return false;
	}
	
}
