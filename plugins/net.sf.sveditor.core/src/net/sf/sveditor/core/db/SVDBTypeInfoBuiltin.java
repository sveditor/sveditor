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

public class SVDBTypeInfoBuiltin extends SVDBTypeInfo {
	public static final int				TypeAttr_Signed				= (1 << 7);
	public static final int				TypeAttr_Unsigned			= (1 << 8);

	private int						fAttr;
	private String					fVectorDim;
	
	public SVDBTypeInfoBuiltin(String typename) {
		super(typename, SVDBDataType.BuiltIn);
	}

	public SVDBTypeInfoBuiltin(String typename, SVDBDataType type) {
		super(typename, type);
	}

	public SVDBTypeInfoBuiltin(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.BuiltIn, file, parent, type, reader);
		fAttr = reader.readInt();
		fVectorDim = reader.readString();
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt(fAttr);
		writer.writeString(fVectorDim);
	}

	public int getAttr() {
		return fAttr;
	}
	
	public void setAttr(int attr) {
		fAttr = attr;
	}
	
	public String getVectorDim() {
		return fVectorDim;
	}
	
	public void setVectorDim(String dim) {
		fVectorDim = dim;
	}
	
	public String toString() {
		String ret = getName();
		
		if ((getAttr() & TypeAttr_Unsigned) != 0) {
			ret += " unsigned";
		}
		
		return ret;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoBuiltin) {
			SVDBTypeInfoBuiltin o = (SVDBTypeInfoBuiltin)obj;
			
			if (fAttr != o.fAttr) {
				return false;
			}
			
			if (fVectorDim == null || o.fVectorDim == null) {
				if (fVectorDim != o.fVectorDim) {
					return false;
				}
			} else if (!fVectorDim.equals(o.fVectorDim)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}

	@Override
	public SVDBTypeInfoBuiltin duplicate() {
		SVDBTypeInfoBuiltin ret = new SVDBTypeInfoBuiltin(getName());
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		SVDBTypeInfoBuiltin o = (SVDBTypeInfoBuiltin)other;
		
		setAttr(o.getAttr());
		setVectorDim(o.getVectorDim());
	}
	
	

}
