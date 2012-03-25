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
import java.util.List;

public class SVDBGenerateRegion extends SVDBChildItem implements ISVDBScopeItem {
	public List<ISVDBChildItem>		fGenerateItems;
	public SVDBLocation				fEndLocation;
	
	public SVDBGenerateRegion() {
		super(SVDBItemType.GenerateRegion);
		fGenerateItems = new ArrayList<ISVDBChildItem>();
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return fGenerateItems;
	}

	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}

	@SuppressWarnings({"unchecked","rawtypes"})
	public List<ISVDBItemBase> getItems() {
		return (List<ISVDBItemBase>)((List)fGenerateItems);
	}

	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fGenerateItems.add(item);
	}

	public void addItem(ISVDBItemBase item) {
		if (item instanceof ISVDBChildItem) {
			((ISVDBChildItem)item).setParent(this);
			fGenerateItems.add((ISVDBChildItem)item);
		}
	}

}
