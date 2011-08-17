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


package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBModportSimplePort extends SVDBChildItem {
	private boolean				fIsMapped;
	private String				fPortId;
	private SVDBExpr			fExpr;
	
	public SVDBModportSimplePort() {
		super(SVDBItemType.ModportSimplePort);
	}
	
	public void setIsMapped(boolean m) {
		fIsMapped = m;
	}
	
	public boolean isMapped() {
		return fIsMapped;
	}
	
	public void setPortId(String id) {
		fPortId = id;
	}
	
	public String getPortId() {
		return fPortId;
	}

	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
}
