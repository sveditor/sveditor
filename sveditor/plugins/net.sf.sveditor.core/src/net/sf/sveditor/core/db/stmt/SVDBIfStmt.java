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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBIfStmt extends SVDBStmt implements ISVDBAddChildItem {
	public SVDBExpr		fCondExpr;
	
	@SVDBDoNotSaveAttr
	private int				fAddIdx;
	
	public SVDBStmt		fIfStmt;
	public SVDBStmt		fElseStmt;
	
	public SVDBIfStmt() {
		super(SVDBItemType.IfStmt);
	}
	
	public SVDBIfStmt(SVDBExpr expr) {
		super(SVDBItemType.IfStmt);
		fCondExpr = expr;
	}
	
	public SVDBExpr getCond() {
		return fCondExpr;
	}
	
	public SVDBStmt getIfStmt() {
		return fIfStmt;
	}
	
	public void setIfStmt(SVDBStmt stmt) {
		fIfStmt = stmt;
	}
	
	public SVDBStmt getElseStmt() {
		return fElseStmt;
	}
	
	public void setElseStmt(SVDBStmt stmt) {
		fElseStmt = stmt;
	}
	
	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx++ == 0) {
			fIfStmt = (SVDBStmt)item;
		} else if (fAddIdx++ == 1) {
			fElseStmt = (SVDBStmt)item;
		}
		if (item != null) {
			item.setParent(this);
		}
	}

	@Override
	public void init(ISVDBItemBase other) {
		SVDBIfStmt o = (SVDBIfStmt)other;
		
		if (o.fCondExpr != null) {
			fCondExpr = o.fCondExpr.duplicate();
		} else {
			fCondExpr = null;
		}
		
		if (o.fIfStmt != null) {
			fIfStmt = o.fIfStmt.duplicate();
		} else {
			fIfStmt = null;
		}
		
		if (o.fElseStmt != null) {
			fElseStmt = o.fElseStmt.duplicate();
		} else {
			fElseStmt = null;
		}

		super.init(other);
	}
	
}
