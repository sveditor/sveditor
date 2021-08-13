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


package org.eclipse.hdt.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBConstraintSetStmt extends SVDBStmt {
	public List<SVDBStmt>				fConstraintList;
	
	public SVDBConstraintSetStmt() {
		super(SVDBItemType.ConstraintSetStmt);
		fConstraintList = new ArrayList<SVDBStmt>();
	}
	
	public List<SVDBStmt> getConstraintList() {
		return fConstraintList;
	}
	
	public void addConstraintStmt(SVDBStmt stmt) {
		fConstraintList.add(stmt);
	}
	
	public SVDBConstraintSetStmt duplicate() {
		return (SVDBConstraintSetStmt)super.duplicate();
	}

}
