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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBModportDecl extends SVDBChildItem implements ISVDBChildParent {
	private List<SVDBModportItem>			fModportItemList;
	
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
