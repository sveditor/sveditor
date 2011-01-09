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

public class SVDBTaskFuncScope extends SVDBScopeItem implements IFieldItemAttr {
	private List<SVDBParamPort>			fParams;
	private int								fAttr;
	private SVDBTypeInfo					fRetType;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBTaskFuncScope(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f,
				SVDBItemType.Function, SVDBItemType.Task);
	}
	
	public SVDBTaskFuncScope(String name, SVDBItemType type) {
		super(name, type);
		fParams = new ArrayList<SVDBParamPort>();
		if (type == SVDBItemType.Function) {
			fRetType = new SVDBTypeInfoBuiltin("void");
		} else {
			fRetType = null;
		}
	}

	public SVDBTaskFuncScope(String name, SVDBTypeInfo ret_type) {
		super(name, SVDBItemType.Function);
		fParams = new ArrayList<SVDBParamPort>();
		fRetType = ret_type;
	}

	@SuppressWarnings("unchecked")
	public SVDBTaskFuncScope(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fParams     = (List<SVDBParamPort>)reader.readItemList(file, this);
		fAttr       = reader.readInt();
		if (getType() == SVDBItemType.Function) {
			fRetType    = (SVDBTypeInfo)reader.readSVDBItem(file, parent);
		} else {
			fRetType    = null;
		}
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeItemList(fParams);
		writer.writeInt(fAttr);
		if (getType() == SVDBItemType.Function) {
			writer.writeSVDBItem(fRetType);
		}
	}
	
	public void setAttr(int attr) {
		fAttr = attr;
	}
	
	public int getAttr() {
		return fAttr;
	}
	
	public void addParam(SVDBParamPort p) {
		p.setParent(this);
		fParams.add(p);
	}
	
	public List<SVDBParamPort> getParams() {
		return fParams;
	}
	
	public void setParams(List<SVDBParamPort> params) {
		fParams = params;
		for (SVDBParamPort p : params) {
			p.setParent(this);
		}
	}
	
	public SVDBTypeInfo getReturnType() {
		return fRetType;
	}
	
	public void setReturnType(SVDBTypeInfo ret) {
		fRetType = ret;
	}
	public SVDBItemBase duplicate() {
		SVDBTaskFuncScope ret = new SVDBTaskFuncScope(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);

		fAttr = ((SVDBTaskFuncScope)other).fAttr;
		fParams.clear();
		for (SVDBParamPort p : ((SVDBTaskFuncScope)other).fParams) {
			fParams.add((SVDBParamPort)p.duplicate());
		}
		
		fRetType = ((SVDBTaskFuncScope)other).fRetType;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTaskFuncScope) {
			SVDBTaskFuncScope o = (SVDBTaskFuncScope)obj;
			
			if (o.fAttr != fAttr) {
				return false;
			}
			
			if (fParams.size() == o.fParams.size()) {
				for (int i=0; i<fParams.size(); i++) {
					if (!fParams.get(i).equals(o.fParams.get(i))) {
						return false;
					}
				}
			} else {
				return false;
			}
			
			if (fRetType == null || o.fRetType == null) {
				if (fRetType != o.fRetType) {
					return false;
				} 
			} else if (!fRetType.equals(o.fRetType)) {
				return false;
			}

			return super.equals(obj);
		}
		return false;
	}

	
}
