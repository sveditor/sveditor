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


package org.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.ISVDBChildParent;
import org.sveditor.core.db.SVDBItemType;

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

	
}
