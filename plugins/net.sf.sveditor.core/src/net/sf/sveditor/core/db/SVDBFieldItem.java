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

public class SVDBFieldItem extends SVDBItem implements IFieldItemAttr {
	
	protected int					fFieldAttr;
	
	public SVDBFieldItem(String name, SVDBItemType type) {
		super(name, type);
	}
	
	public SVDBFieldItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fFieldAttr = reader.readInt();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt(fFieldAttr);
	}
	
	public int getAttr() {
		return fFieldAttr;
	}
	
	public void setAttr(int attr) {
		fFieldAttr = attr;
	}
	
	public SVDBItemBase duplicate() {
		SVDBFieldItem ret = new SVDBFieldItem(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public boolean equals(Object obj) {
		if (obj instanceof SVDBFieldItem) {
			boolean ret = super.equals(obj);
			ret &= ((SVDBFieldItem)obj).fFieldAttr == fFieldAttr;
			return ret;
		}
		return false;
	}

	public void init(SVDBItemBase other) {
		super.init(other);
		
		fFieldAttr = ((SVDBFieldItem)other).fFieldAttr;
	}

}
