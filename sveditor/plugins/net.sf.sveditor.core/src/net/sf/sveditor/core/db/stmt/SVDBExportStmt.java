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


package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBExportStmt extends SVDBStmt implements ISVDBChildParent {
	public List<SVDBExportItem>			fExportList;
	
	public SVDBExportStmt() {
		super(SVDBItemType.ExportStmt);
		fExportList = new ArrayList<SVDBExportItem>();
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fExportList.add((SVDBExportItem)item);
	}

	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fExportList.iterator();
			}
		};
	}

}
