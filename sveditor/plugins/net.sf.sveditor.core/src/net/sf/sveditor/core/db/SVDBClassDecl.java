/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


public class SVDBClassDecl extends SVDBScopeItem {
	
	public List<SVDBModIfcClassParam>			fParams;
	public SVDBTypeInfoClassType				fClassType;
	public SVDBTypeInfoClassType				fSuperClass;
	public List<SVDBTypeInfoClassType>			fImplements;

	public SVDBClassDecl() {
		this("");
	}
	
	public SVDBClassDecl(String name) {
		super(name, SVDBItemType.ClassDecl);
	}

	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public void addParameters(List<SVDBModIfcClassParam> params) {
		if (fParams == null) {
			fParams = new ArrayList<SVDBModIfcClassParam>();
		}
		for (SVDBModIfcClassParam p : params) {
			p.setParent(this);
			fParams.add(p);
		}
	}
	
	public SVDBTypeInfoClassType getClassType() {
		return fClassType;
	}
	
	public void setClassType(SVDBTypeInfoClassType cls_type) {
		fClassType = cls_type;
	}

	public SVDBTypeInfoClassType getSuperClass() {
		return fSuperClass;
	}
	
	public void setSuperClass(SVDBTypeInfoClassType super_class) {
		fSuperClass = super_class;
	}
	
	public void addImplements(SVDBTypeInfoClassType impl) {
		if (fImplements == null) {
			fImplements = new ArrayList<SVDBTypeInfoClassType>();
		}
		fImplements.add(impl);
	}
	
	public List<SVDBTypeInfoClassType> getImplements() {
		return fImplements;
	}
	
	public SVDBClassDecl duplicate() {
		return (SVDBClassDecl)SVDBItemUtils.duplicate(this);
	}

	public void init(SVDBItemBase other) {
		super.init(other);
		SVDBClassDecl o = (SVDBClassDecl)other;

		if (o.fParams != null) {
			fParams = new ArrayList<SVDBModIfcClassParam>();
			for (SVDBModIfcClassParam p : o.fParams) {
				fParams.add(p);
			}
		} else {
			fParams = null;
		}
		
		setSuperClass(o.getSuperClass());
	}

	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBClassDecl) {
			SVDBClassDecl o = (SVDBClassDecl)obj;

			if (fParams == null || o.fParams == null) {
				if (fParams != o.fParams) {
					return false;
				}
			} else {
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
			}
			
			if (fSuperClass == null || o.fSuperClass == null) {
				if (fSuperClass != o.fSuperClass) {
					return false;
				}
			} else if (!fSuperClass.equals(o.fSuperClass)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}
	 */

}
