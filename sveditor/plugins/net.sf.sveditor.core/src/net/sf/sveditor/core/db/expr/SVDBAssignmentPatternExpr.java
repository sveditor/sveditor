/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBAssignmentPatternExpr extends SVDBExpr {
	public List<SVDBExpr>			fPatternList;
	
	public SVDBAssignmentPatternExpr() {
		this(SVDBItemType.AssignmentPatternExpr);
	}

	public SVDBAssignmentPatternExpr(SVDBItemType type) {
		super(type);
		fPatternList = new ArrayList<SVDBExpr>();
	}

	public List<SVDBExpr> getPatternList() {
		return fPatternList;
	}
	
	public SVDBAssignmentPatternExpr duplicate() {
		return (SVDBAssignmentPatternExpr)super.duplicate();
	}
	
	public void init(SVDBItemBase other) {
		
	}

}
