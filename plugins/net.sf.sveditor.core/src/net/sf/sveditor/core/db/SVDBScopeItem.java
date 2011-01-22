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

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBScopeItem extends SVDBItem implements ISVDBScopeItem {
	protected List<ISVDBItemBase>		fItems;
	protected SVDBLocation				fEndLocation;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBScopeItem(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, 
				SVDBItemType.Property, SVDBItemType.Sequence); 
	}
	
	
	public SVDBScopeItem(String name, SVDBItemType type) {
		super(name, type);
		
		fItems = new ArrayList<ISVDBItemBase>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBScopeItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		if (getType() == SVDBItemType.File) {
			file   = (SVDBFile)this;
		}
		fEndLocation = new SVDBLocation(reader.readInt(), reader.readInt());
		fItems = (List<ISVDBItemBase>)reader.readItemList(file, this);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt((fEndLocation!=null)?fEndLocation.getLine():0);
		writer.writeInt((fEndLocation!=null)?fEndLocation.getPos():0);
		writer.writeItemList(fItems);
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

	public void addItems(List<SVDBItem> items) {
		for (SVDBItem item : items) {
			addItem(item);
		}
	}

	public List<ISVDBItemBase> getItems() {
		return fItems;
	}

	public SVDBItemBase duplicate() {
		SVDBScopeItem ret = new SVDBScopeItem(getName(), getType());

		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBScopeItem si = (SVDBScopeItem)other;
		
		fItems.clear();
		for (ISVDBItemBase it : si.getItems()) {
			fItems.add((SVDBItem)it.duplicate());
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
