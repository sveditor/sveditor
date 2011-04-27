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
	protected List<ISVDBItemBase>		fItems;
	protected SVDBLocation				fEndLocation;
	
	protected SVDBScopeItem(String name, SVDBItemType type) {
		super(name, type);
		
		fItems = new ArrayList<ISVDBItemBase>();
	}
	
	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}
	
	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}
	
	public void addItem(ISVDBChildItem item) {
		item.setParent(this);
		fItems.add(item);
	}

	public void addItems(List<ISVDBChildItem> items) {
		for (ISVDBChildItem item : items) {
			addItem(item);
		}
	}

	/**
	 * getItems() is replaced by getChildren()
	 */
	@Deprecated
	public List<ISVDBItemBase> getItems() {
		return fItems;
	}
	
	public Iterable<ISVDBItemBase> getChildren() {
		return fItems;
	}

	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBScopeItem si = (SVDBScopeItem)other;
		
		fItems.clear();
		for (ISVDBItemBase it : si.getItems()) {
			fItems.add(it.duplicate());
		}
		if (((SVDBScopeItem)other).fEndLocation != null) {
			fEndLocation = new SVDBLocation(
				((SVDBScopeItem)other).fEndLocation);
		} else {
			fEndLocation = null;
		}
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
