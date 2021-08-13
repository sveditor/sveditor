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
package org.eclipse.hdt.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBForeachLoopvarExpr extends SVDBExpr {
	public SVDBExpr				fId;
	public List<SVDBExpr>		fLoopVarList;
	
	public SVDBForeachLoopvarExpr() {
		super(SVDBItemType.ForeachLoopvarExpr);
		fLoopVarList = new ArrayList<SVDBExpr>();
	}
	
	public void setId(SVDBExpr id) {
		fId = id;
	}
	
	public void addLoopVar(SVDBExpr loopvar) {
		fLoopVarList.add(loopvar);
	}

}
