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
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBImportStmt extends SVDBStmt implements ISVDBChildParent {
	
	private List<SVDBImportItem>			fImportList;
	
	public SVDBImportStmt() {
		super(SVDBItemType.ImportStmt);
		fImportList = new ArrayList<SVDBImportItem>();
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fImportList.add((SVDBImportItem)item);
	}
	
	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fImportList.iterator();
			}
		};
	}
}
