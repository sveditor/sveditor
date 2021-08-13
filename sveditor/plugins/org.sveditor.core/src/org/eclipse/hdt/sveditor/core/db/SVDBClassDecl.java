/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;


public class SVDBClassDecl extends SVDBScopeItem {
	
	public List<SVDBModIfcClassParam>			fParams;
	public SVDBTypeInfoClassType				fClassType;
	public List<SVDBTypeInfoClassType>			fSuperClassList;
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
		return (fSuperClassList != null)?fSuperClassList.get(0):null;
	}
	
	public List<SVDBTypeInfoClassType> getSuperClassList() {
		return fSuperClassList;
	}
	
	public void addSuperClass(SVDBTypeInfoClassType super_class) {
		if (fSuperClassList == null) {
			fSuperClassList = new ArrayList<SVDBTypeInfoClassType>();
		}
		fSuperClassList.add(super_class);
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
		
		addSuperClass(o.getSuperClass());
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
