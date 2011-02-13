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

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;


public class SVDBItem extends SVDBItemBase implements ISVDBNamedItem {
	protected ISVDBChildItem		fParent;
	protected String				fName;
	
	public SVDBItem(String name, SVDBItemType type) {
		super(type);
		if (name == null) {
			fName = "";
		} else {
			fName = name;
		}
	}
	
	public SVDBItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(type);
		fParent   = parent;
		fName     = reader.readString();
		fLocation = new SVDBLocation(reader.readInt(), reader.readInt());
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fName);
		writer.writeInt((fLocation != null)?fLocation.getLine():0);
		writer.writeInt((fLocation != null)?fLocation.getPos():0);
	}
	
	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}
	
	public ISVDBChildItem getParent() {
		return fParent;
	}
	
	public Iterable<ISVDBItemBase> getChildren() {
		return EmptySVDBItemIterable.iterable;
	}

	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public void setType(SVDBItemType type) {
		fType = type;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public SVDBItemBase duplicate() {
		SVDBItem ret = new SVDBItem(fName, fType);
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		SVDBItem o = (SVDBItem)other;
		fName     = o.fName;
		fParent   = o.fParent;
		super.init(o);
	}
	
	public boolean equals(Object obj) {
		if (obj == this) {
			return true;
		} else if (obj instanceof SVDBItem) {
			return equals((SVDBItem)obj, true);
		} else {
			return super.equals(obj);
		}
	}

	@Override
	public boolean equals(ISVDBItemBase obj, boolean full) {
		SVDBItem other = (SVDBItem)obj;
		boolean ret = true;
		
		if (other.fName == null || fName == null) {
			ret &= other.fName == fName;
		} else {
			ret &= other.fName.equals(fName);
		}
		
		ret &= super.equals(obj, full);
		
		return ret;
	}
	
	public static String getName(ISVDBItemBase item) {
		if (item instanceof ISVDBNamedItem) {
			return ((ISVDBNamedItem)item).getName();
		} else {
			return "UNKNOWN " + item.getType();
		}
	}
	
}
