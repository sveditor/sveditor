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
import java.util.List;

public class SVDBScopeItem extends SVDBItem implements ISVDBScopeItem {
	public List<ISVDBChildItem>		fItems;
	public SVDBLocation				fEndLocation;
	
	protected SVDBScopeItem(String name, SVDBItemType type) {
		super(name, type);
		
		fItems = new ArrayList<ISVDBChildItem>();
	}
	
	public SVDBScopeItem() {
		super("", SVDBItemType.NullExpr);
		fItems = new ArrayList<ISVDBChildItem>();
	}
	
	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}
	
	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	
	public void addItem(ISVDBItemBase item) {
		if (item instanceof ISVDBChildItem) {
			((ISVDBChildItem)item).setParent(this);
			fItems.add((ISVDBChildItem)item);
		} else {
			throw new RuntimeException("Failed to add non-child item " + item.getClass().getName());
		}
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fItems.add(item);
	}

	/**
	 * getItems() is replaced by getChildren()
	 */
	@Deprecated
	@SuppressWarnings({"unchecked","rawtypes"})
	public List<ISVDBItemBase> getItems() {
		return (List<ISVDBItemBase>)((List)fItems);
	}
	
	public Iterable<ISVDBChildItem> getChildren() {
		return fItems;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBScopeItem) {
			SVDBScopeItem o = (SVDBScopeItem)obj;
			
			if (fEndLocation == null || o.fEndLocation == null) {
				if (fEndLocation != o.fEndLocation) {
					return false;
				}
			} else if (!fEndLocation.equals(o.fEndLocation)) {
				return false;
			}
					
			if (fItems.size() == o.fItems.size()) {
				for (int i=0; i<fItems.size(); i++) {
					if (!fItems.get(i).equals(o.fItems.get(i))) {
						return false;
					}
				}
			} else {
				return false;
			}
			
			return super.equals(obj);
		}
		
		return false;
	}
	
}
