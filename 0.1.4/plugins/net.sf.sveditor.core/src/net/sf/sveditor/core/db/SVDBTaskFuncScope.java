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

public class SVDBTaskFuncScope extends SVDBScopeItem implements IFieldItemAttr {
	private List<SVDBTaskFuncParam>			fParams;
	private int								fAttr;
	private String							fRetType;
	
	public SVDBTaskFuncScope(String name, SVDBItemType type) {
		super(name, type);
		fParams = new ArrayList<SVDBTaskFuncParam>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBTaskFuncScope(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fParams     = (List<SVDBTaskFuncParam>)reader.readItemList(file, this);
		fAttr       = reader.readInt();
		fRetType    = reader.readString();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeItemList(fParams);
		writer.writeInt(fAttr);
		writer.writeString(fRetType);
	}
	
	public void setAttr(int attr) {
		fAttr = attr;
	}
	
	public int getAttr() {
		return fAttr;
	}
	
	public void addParam(SVDBTaskFuncParam p) {
		p.setParent(this);
		fParams.add(p);
	}
	
	public List<SVDBTaskFuncParam> getParams() {
		return fParams;
	}
	
	public String getReturnType() {
		return fRetType;
	}
	
	public void setReturnType(String ret) {
		fRetType = ret;
	}
	public SVDBItem duplicate() {
		SVDBTaskFuncScope ret = new SVDBTaskFuncScope(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);

		fAttr = ((SVDBTaskFuncScope)other).fAttr;
		fParams.clear();
		for (SVDBTaskFuncParam p : ((SVDBTaskFuncScope)other).fParams) {
			fParams.add((SVDBTaskFuncParam)p.duplicate());
		}
		
		fRetType = ((SVDBTaskFuncScope)other).fRetType;
	}
	
}
