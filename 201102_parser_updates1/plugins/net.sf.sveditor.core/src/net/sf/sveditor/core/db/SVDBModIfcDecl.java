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

import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;

public class SVDBModIfcDecl extends SVDBScopeItem {
	
	private List<SVDBModIfcClassParam>			fParams;
	private List<SVDBParamPortDecl>					fPorts;
	
	protected SVDBModIfcDecl(String name, SVDBItemType type) {
		super(name, type);
		
		fParams = new ArrayList<SVDBModIfcClassParam>();
		fPorts = new ArrayList<SVDBParamPortDecl>();
	}
	
	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public List<SVDBParamPortDecl> getPorts() {
		return fPorts;
	}
	
	public boolean isParameterized() {
		// TODO: should consider super-class parameterization?
		return (fParams != null && fParams.size() > 0);
	}
	
	public SVDBModIfcDecl duplicate() {
		SVDBModIfcDecl ret = new SVDBModIfcDecl(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
		SVDBModIfcDecl o = (SVDBModIfcDecl)other;

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
		if (obj instanceof SVDBModIfcDecl) {
			SVDBModIfcDecl o = (SVDBModIfcDecl)obj;
			
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
