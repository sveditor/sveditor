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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFirstMatchExpr extends SVDBExpr {
	SVDBExpr				fExpr;
	List<SVDBExpr>			fSequenceMatchItems;		

	public SVDBFirstMatchExpr() {
		super(SVDBItemType.FirstMatchExpr);
		fSequenceMatchItems = new ArrayList<SVDBExpr>();
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void addSequenceMatchItem(SVDBExpr expr) {
		fSequenceMatchItems.add(expr);
	}
	
	public List<SVDBExpr> getSequenceMatchItems() {
		return fSequenceMatchItems;
	}
	
}
