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
import net.sf.sveditor.core.db.stmt.SVDBParamPort;

public class SVDBModIfcClassDecl extends SVDBScopeItem {
	
	private List<SVDBModIfcClassParam>			fParams;
	private List<SVDBParamPort>					fPorts;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBModIfcClassDecl(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f,
				SVDBItemType.Module, SVDBItemType.Interface,
				SVDBItemType.Struct, SVDBItemType.Program); 
	}
	
	public SVDBModIfcClassDecl(String name, SVDBItemType type) {
		super(name, type);
		
		fParams = new ArrayList<SVDBModIfcClassParam>();
		fPorts = new ArrayList<SVDBParamPort>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBModIfcClassDecl(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fParams     = (List<SVDBModIfcClassParam>)reader.readItemList(this);
		fPorts = (List<SVDBParamPort>)reader.readItemList(this);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeItemList(fParams);
		writer.writeItemList(fPorts);
	}
	
	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public List<SVDBParamPort> getPorts() {
		return fPorts;
	}
	
	public boolean isParameterized() {
		// TODO: should consider super-class parameterization?
		return (fParams != null && fParams.size() > 0);
	}
	
	public SVDBModIfcClassDecl duplicate() {
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
		
		fPorts.clear();
		fPorts.addAll(o.fPorts);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBModIfcClassDecl) {
			SVDBModIfcClassDecl o = (SVDBModIfcClassDecl)obj;
			
			if (fParams.size() == o.fParams.size()) {
				for (int i=0; i<fParams.size(); i++) {
					SVDBModIfcClassParam p1 = fParams.get(i);
					SVDBModIfcClassParam p2 = o.fParams.get(i);
					
					if (!p1.equals(p2)) {
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
