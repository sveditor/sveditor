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

public class SVDBAssociativeArrayAssignExpr extends SVDBExpr {
	public List<SVDBAssociativeArrayElemAssignExpr>		fElements;
	
	public SVDBAssociativeArrayAssignExpr() {
		super(SVDBItemType.AssociativeArrayAssignExpr);
		fElements = new ArrayList<SVDBAssociativeArrayElemAssignExpr>();
	}
	
	public void addElement(SVDBAssociativeArrayElemAssignExpr elem) {
		fElements.add(elem);
	}

}
