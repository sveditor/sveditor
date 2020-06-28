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


package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFirstMatchExpr extends SVDBExpr {
	public SVDBExpr				fExpr;
	public List<SVDBExpr>			fSequenceMatchItems;		

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
