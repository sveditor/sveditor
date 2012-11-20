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

import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBGenerateIf extends SVDBChildItem implements ISVDBAddChildItem {
	@SVDBDoNotSaveAttr
	int				fAddIdx;
	public SVDBExpr		fExpr;
	public ISVDBChildItem	fIfBody;
	public ISVDBChildItem	fElseBody;
	public String			fName;

	public SVDBGenerateIf() {
		super(SVDBItemType.GenerateIf);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public ISVDBChildItem getIfBody() {
		return fIfBody;
	}
	
	public ISVDBChildItem getElseBody() {
		return fElseBody;
	}

	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx == 0) {
			fIfBody = item;
		} else if (fAddIdx == 1) {
			fElseBody = item;
		}
		fAddIdx++;
	}

	
}
