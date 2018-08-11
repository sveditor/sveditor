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


package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBDefParamStmt extends SVDBStmt implements ISVDBChildParent {
	public List<SVDBDefParamItem>		fParamAssignList;
	
	public SVDBDefParamStmt() {
		super(SVDBItemType.DefParamStmt);
		fParamAssignList = new ArrayList<SVDBDefParamItem>();
	}
	
	public List<SVDBDefParamItem> getParamAssignList() {
		return fParamAssignList;
	}
	
	public void addParamAssign(SVDBDefParamItem item) {
		fParamAssignList.add(item);
	}

	@Override
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fParamAssignList.add((SVDBDefParamItem)item);
	}

	@SuppressWarnings({"unchecked","rawtypes"})
	@Override
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			
			@Override
			public Iterator<ISVDBChildItem> iterator() {
				// TODO Auto-generated method stub
				return (Iterator)fParamAssignList.iterator();
			}
		};
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_def_param_stmt(this);
	}
	
}
