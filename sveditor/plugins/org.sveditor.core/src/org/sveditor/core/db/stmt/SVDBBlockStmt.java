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
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.ISVDBScopeItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.attr.SVDBParentAttr;

public class SVDBBlockStmt extends SVDBStmt implements ISVDBScopeItem {
	@SVDBParentAttr
	public ISVDBChildItem			fParent;
	
	public List<ISVDBItemBase>		fItems;
	public long						fEndLocation;
	public String					fBlockName;
	
	public SVDBBlockStmt() {
		super(SVDBItemType.BlockStmt);
		fBlockName = "";
		fItems = new ArrayList<ISVDBItemBase>();
	}

	public SVDBBlockStmt(SVDBItemType type) {
		super(type);
		fBlockName = "";
		fItems = new ArrayList<ISVDBItemBase>();
	}

	
	public void addChildItem(ISVDBChildItem item) {
		fItems.add(item);
		if (item != null) {
			item.setParent(this);
		}
	}
	
	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fItems.iterator();
			}
		};
	}

	public void addItem(ISVDBItemBase item) {
		fItems.add(item);
		if (item != null && item instanceof ISVDBChildItem) {
			((ISVDBChildItem)item).setParent(this);
		}
	}

	public String getBlockName() {
		return fBlockName;
	}
	
	public void setBlockName(String name) {
		fBlockName = name;
	}

	public ISVDBChildItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

	public long getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(long loc) {
		fEndLocation = loc;
	}

	public List<ISVDBItemBase> getItems() {
		return fItems;
	}

	@Override
	public SVDBBlockStmt duplicate() {
		return (SVDBBlockStmt)super.duplicate();
	}

	@Override
	public void init(ISVDBItemBase other) {
		SVDBBlockStmt o = (SVDBBlockStmt)other;
		super.init(other);
		
		fBlockName = o.getBlockName();
		if (o.getEndLocation() == -1) {
			fEndLocation = -1;
		} else {
			fEndLocation = o.getEndLocation();
		}
		fItems.clear();
		for (ISVDBItemBase i : o.getItems()) {
			fItems.add(i.duplicate());
		}
		fParent = o.getParent();
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		if (!super.equals(obj, full)) {
			return false;
		}
		
		boolean ret = true;
		
		// TODO:
		
		return ret;
	}

	
}
