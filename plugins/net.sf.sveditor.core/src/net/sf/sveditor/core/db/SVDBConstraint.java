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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBConstraint extends SVDBScopeItem {
	List<SVDBStmt>		fConstraintList;
	
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
