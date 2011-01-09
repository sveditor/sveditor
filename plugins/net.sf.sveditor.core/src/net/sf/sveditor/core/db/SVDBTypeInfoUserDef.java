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

import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;


public class SVDBTypeInfoUserDef extends SVDBTypeInfo implements ISVDBScopeItem {
	protected SVDBParamValueAssignList				fParamAssignList;
	protected SVDBLocation							fEndLocation;
	protected List<SVDBItem>						fItems;
	
	public SVDBTypeInfoUserDef(String typename) {
		this(typename, SVDBDataType.UserDefined);
	}
	
	public SVDBTypeInfoUserDef(String typename, SVDBDataType type) {
		super(typename, type);
	}
	
	public SVDBTypeInfoUserDef(
			SVDBDataType 	dt, 
			SVDBFile 		file, 
			SVDBScopeItem 	parent, 
			SVDBItemType 	type, 
			IDBReader 		reader) throws DBFormatException {
		super(dt, file, parent, type, reader);
		fParamAssignList = (SVDBParamValueAssignList)reader.readSVDBItem(file, parent);
	}
	
	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public List<SVDBItem> getItems() {
		return fItems;
	}

	public void setEndLocation(SVDBLocation loc) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeSVDBItem(fParamAssignList);
	}

	public SVDBParamValueAssignList getParameters() {
		return fParamAssignList;
	}

	public void setParameters(SVDBParamValueAssignList params) {
		fParamAssignList = params;
	}
	
	public String toString() {
		StringBuilder ret = new StringBuilder();
		ret.append(getName());
		
		if (fParamAssignList != null && fParamAssignList.getParameters().size() > 0) {
			ret.append(" #(");
			
			for (SVDBParamValueAssign p : fParamAssignList.getParameters()) {
				if (fParamAssignList.getIsNamedMapping()) {
					ret.append("." + p.getName() + "(" + p.getValue() + "), ");
				} else {
					ret.append(p.getValue() + ", ");
				}
			}
			
			ret.setLength(ret.length()-2);
			ret.append(")");
		}
		
		return ret.toString();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoUserDef) {
			SVDBTypeInfoUserDef o = (SVDBTypeInfoUserDef)obj;
			
			if (fParamAssignList == null || o.fParamAssignList == null) {
				if (fParamAssignList != o.fParamAssignList) {
					return false;
				}
			} else if (fParamAssignList.equals(o.fParamAssignList)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBTypeInfoUserDef ret = new SVDBTypeInfoUserDef(getName(), getDataType());
		
		if (fParamAssignList != null) {
			ret.setParameters((SVDBParamValueAssignList)getParameters().duplicate());
		}
		
		return ret;
	}
	
}
