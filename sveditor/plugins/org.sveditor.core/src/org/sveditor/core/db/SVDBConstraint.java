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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.sveditor.core.db.stmt.SVDBStmt;

public class SVDBConstraint extends SVDBScopeItem {
	public List<SVDBStmt>		fConstraintList;
	
	public SVDBConstraint() {
		super("", SVDBItemType.Constraint);
		fConstraintList = new ArrayList<SVDBStmt>();
	}

	public void addChildItem(ISVDBChildItem stmt) {
		stmt.setParent(this);
		fConstraintList.add((SVDBStmt)stmt);
	}

	@Override
	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fConstraintList.iterator();
			}
		};
	}
	
	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBConstraint) {
			return ((SVDBConstraint)obj).fConstraintExpr.equals(fConstraintExpr) &&
				super.equals(obj);
		}
		return false;
	}
	 */
	
}
