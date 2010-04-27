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


public class SVDBItem {
	private SVDBScopeItem			fParent;
	private String					fName;
	private SVDBItemType			fType;
	private SVDBLocation			fLocation;
	
	public SVDBItem(String name, SVDBItemType type) {
		if (name == null) {
			fName = "";
		} else {
			fName = name;
		}
		fType = type;
		fLocation = null;
	}
	
	public SVDBItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		fParent   = parent;
		fType     = type;
		fName     = reader.readString();
		fLocation = new SVDBLocation(file, reader.readInt(), 0);
	}
	
	public void dump(IDBWriter writer) {
		writer.writeItemType(fType);
		writer.writeString(fName);
		writer.writeInt((fLocation != null)?fLocation.getLine():0);
	}
	
	public SVDBLocation getLocation() {
		return fLocation;
	}
	
	public void setLocation(SVDBLocation loc) {
		fLocation = loc;
	}
	
	public void setParent(SVDBScopeItem parent) {
		fParent = parent;
	}
	
	public SVDBScopeItem getParent() {
		return fParent;
	}

	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBItem(fName, fType);
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		fName     = other.fName;
		fParent   = other.fParent;
		fType     = other.fType;
		fLocation = new SVDBLocation(other.fLocation);
	}
	
	public boolean equals(Object obj) {
		if (obj == this) {
			return true;
		} else if (obj instanceof SVDBItem) {
			SVDBItem other = (SVDBItem)obj;
			boolean ret = true;
			
			if (other.fName == null || fName == null) {
				ret &= other.fName == fName;
			} else {
				ret &= other.fName.equals(fName);
			}
			if (other.fType == null || fType == null) {
				ret &= other.fType == fType;
			} else {
				ret &= other.fType.equals(fType);
			}
			
			return ret;
		} else {
			return super.equals(obj);
		}
	}
	
}
