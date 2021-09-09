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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBModportDecl extends SVDBChildItem implements ISVDBChildParent {
	public List<SVDBModportItem>			fModportItemList;
	
	public SVDBModportDecl() {
		super(SVDBItemType.ModportDecl);
		fModportItemList = new ArrayList<SVDBModportItem>();
	}
	
	public List<SVDBModportItem> getModportItemList() {
		return fModportItemList;
	}
	
	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fModportItemList.iterator();
			}
		};
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fModportItemList.add((SVDBModportItem)item);
	}

	public void addModportItem(SVDBModportItem item) {
		item.setParent(this);
		fModportItemList.add(item);
	}

}
