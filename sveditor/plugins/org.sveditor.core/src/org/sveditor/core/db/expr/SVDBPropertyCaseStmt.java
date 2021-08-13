/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.SVDBItemType;

public class SVDBPropertyCaseStmt extends SVDBExpr {
	
	public SVDBExpr						fExpr;
	public List<SVDBPropertyCaseItem>	fItemList;
	
	public SVDBPropertyCaseStmt() {
		super(SVDBItemType.PropertyCaseStmt);
		fItemList = new ArrayList<SVDBPropertyCaseItem>();
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void addItem(SVDBPropertyCaseItem item) {
		fItemList.add(item);
	}

}
