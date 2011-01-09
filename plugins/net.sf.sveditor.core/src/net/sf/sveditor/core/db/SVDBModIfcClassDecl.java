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

public class SVDBModIfcClassDecl extends SVDBScopeItem {
	
	private List<SVDBModIfcClassParam>			fParams;
	private String								fSuperClass;
	private List<SVDBModIfcClassParam>			fSuperParams;
	private List<SVDBParamPort>					fPorts;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBModIfcClassDecl(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f,
				SVDBItemType.Class, SVDBItemType.Module, SVDBItemType.Interface,
				SVDBItemType.Struct, SVDBItemType.Program); 
	}
	
	public SVDBModIfcClassDecl(String name, SVDBItemType type) {
		super(name, type);
		
		fParams = new ArrayList<SVDBModIfcClassParam>();
		fSuperParams = new ArrayList<SVDBModIfcClassParam>();
		fPorts = new ArrayList<SVDBParamPort>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBModIfcClassDecl(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fParams     = (List<SVDBModIfcClassParam>)reader.readItemList(file, this);
		fSuperClass = reader.readString();
		fSuperParams = (List<SVDBModIfcClassParam>)reader.readItemList(file, this);
		fPorts = (List<SVDBParamPort>)reader.readItemList(file, this);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeItemList(fParams);
		writer.writeString(fSuperClass);
		writer.writeItemList(fSuperParams);
		writer.writeItemList(fPorts);
	}
	
	
	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public List<SVDBModIfcClassParam> getSuperParameters() {
		return fSuperParams;
	}
	
	public List<SVDBParamPort> getPorts() {
		return fPorts;
	}
	
	public boolean isParameterized() {
		return ((fParams != null && fParams.size() > 0) ||
				(fSuperParams != null && fSuperParams.size() > 0));
	}
	
	public String getSuperClass() {
		return fSuperClass;
	}
	
	public void setSuperClass(String super_class) {
		fSuperClass = super_class;
	}
	
	public SVDBItemBase duplicate() {
		SVDBModIfcClassDecl ret = new SVDBModIfcClassDecl(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		SVDBModIfcClassDecl o = (SVDBModIfcClassDecl)other;

		if (o.fParams != null) {
			fParams.clear();
			for (SVDBModIfcClassParam p : o.fParams) {
				fParams.add((SVDBModIfcClassParam)p.duplicate());
			}
		} else {
			fParams = null;
		}
		
		setSuperClass(o.getSuperClass());
		if (o.fSuperParams == null) {
			fSuperParams = null;
		} else {
			fSuperParams.clear();
			for (SVDBModIfcClassParam p : o.fSuperParams) {
				fSuperParams.add((SVDBModIfcClassParam)p.duplicate());
			}
		}
		
		fPorts.clear();
		fPorts.addAll(o.fPorts);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBModIfcClassDecl) {
			SVDBModIfcClassDecl o = (SVDBModIfcClassDecl)obj;
			
			if (fParams.size() == o.fParams.size()) {
				for (int i=0; i<fParams.size(); i++) {
					if (!fParams.get(i).equals(o.fParams.get(i))) {
						return false;
					}
				}
			} else {
				return false;
			}
			
			if (fSuperClass == null || o.fSuperClass == null) {
				if (fSuperClass != o.fSuperClass) {
					return false;
				}
			} else if (!fSuperClass.equals(o.fSuperClass)) {
				return false;
			}
			
			if (fSuperParams == null || o.fSuperParams == null) {
				if (fSuperParams != o.fSuperParams) {
					return false;
				}
			} else {
				if (fSuperParams.size() == o.fSuperParams.size()) {
					for (int i=0; i<fSuperParams.size(); i++) {
						if (!fSuperParams.get(i).equals(o.fSuperParams.get(i))) {
							return false;
						}
					}
				} else {
					return false;
				}
			}
			
			return super.equals(obj);
		}
		return false;
	}
	
}
