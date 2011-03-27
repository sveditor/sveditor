/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAlwaysStmt extends SVDBBodyStmt {
	
	public enum AlwaysType {
		Always,
		AlwaysComb,
		AlwaysLatch,
		AlwaysFF
	};
	
	public enum AlwaysEventType {
		None, // always ... 
		Any,  // @(*)
		Expr // always @(a or b or c)
	}
	
	private AlwaysType			fAlwaysType;
	private AlwaysEventType		fAlwaysEventType;
	private SVDBExpr			fAlwaysEventExpr;
	
	public SVDBAlwaysStmt() {
		this(AlwaysType.Always);
	}
	
	public SVDBAlwaysStmt(AlwaysType type) {
		super(SVDBItemType.AlwaysStmt);
		fAlwaysType = type;
	}
	
	public AlwaysType getAlwaysType() {
		return fAlwaysType;
	}
	
	public AlwaysEventType getAlwaysEventType() {
		return fAlwaysEventType;
	}
	
	public void setAlwaysEventType(AlwaysEventType type) {
		fAlwaysEventType = type;
	}
	
	public SVDBExpr getEventExpr() {
		return fAlwaysEventExpr;
	}
	
	public void setEventExpr(SVDBExpr expr) {
		fAlwaysEventExpr = expr;
	}
	
	@Override
	public SVDBAlwaysStmt duplicate() {
		SVDBAlwaysStmt ret = new SVDBAlwaysStmt(fAlwaysType);
		
		ret.init(this);
		
		return ret;
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
