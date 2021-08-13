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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import org.sveditor.core.db.expr.SVDBExpr;

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
	
	public Iterable<ISVDBChildItem> getChildren()  {
		List<ISVDBChildItem> ci = new ArrayList<ISVDBChildItem>();
		if (fAddIdx > 0)  {
			ci.add(fIfBody);
		}
		if (fAddIdx > 1)  {
			ci.add(fElseBody);
		}
		return (ci);
	}

	
}
