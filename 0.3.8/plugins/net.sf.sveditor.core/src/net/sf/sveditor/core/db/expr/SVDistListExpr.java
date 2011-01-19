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


package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemBase;

public class SVDistListExpr extends SVExpr {
	private SVExpr							fLHS;
	private List<SVDistItemExpr>			fDistItems;
	
	public SVDistListExpr() {
		super(SVExprType.DistList);
		fDistItems = new ArrayList<SVDistItemExpr>();
	}
	
	public void setLHS(SVExpr lhs) {
		fLHS = lhs;
	}
	
	public SVExpr getLHS() {
		return fLHS;
	}
	
	public List<SVDistItemExpr> getDistItems() {
		return fDistItems;
	}
	
	public void addDistItem(SVDistItemExpr item) {
		fDistItems.add(item);
	}
	
	public SVDBItemBase duplicate() {
		SVDistListExpr ret = new SVDistListExpr();
		ret.getDistItems().addAll(fDistItems);
		ret.setLHS((SVExpr)fLHS.duplicate());
		
		return ret;
	}

}
