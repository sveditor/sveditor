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
import java.util.List;

public class SVDBGenerateRegion extends SVDBChildItem implements ISVDBScopeItem {
	public List<ISVDBChildItem>		fGenerateItems;
	public long						fEndLocation;
	
	public SVDBGenerateRegion() {
		super(SVDBItemType.GenerateRegion);
		fGenerateItems = new ArrayList<ISVDBChildItem>();
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return fGenerateItems;
	}

	public long getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(long loc) {
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
