/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;

public class SVDBParamValueAssignList extends SVDBItem implements ISVDBEndLocation {
	
	public boolean							fNamedMapping;
	public List<SVDBParamValueAssign>		fParameters;
	public SVDBLocation					fEndLocation;
	
	public SVDBParamValueAssignList() {
		super("", SVDBItemType.ParamValueAssignList);
		fNamedMapping = false;
		fParameters = new ArrayList<SVDBParamValueAssign>();
	}
	
	public void setEndLocation(SVDBLocation l) {
		fEndLocation = l;
	}
	
	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public List<SVDBParamValueAssign> getParameters() {
		return fParameters;
	}
	
	public void addParameter(SVDBParamValueAssign assign) {
		fParameters.add(assign);
	}

	public void addParameter(String name, String val) {
		SVDBParamValueAssign assign = new SVDBParamValueAssign(name, new SVDBIdentifierExpr(val));
		fParameters.add(assign);
	}

	public boolean getIsNamedMapping() {
		return fNamedMapping;
	}
	
	public void setIsNamedMapping(boolean m) {
		fNamedMapping = m;
	}
	
	@Override
	public SVDBParamValueAssignList duplicate() {
		return (SVDBParamValueAssignList)super.duplicate();
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		
		fNamedMapping = ((SVDBParamValueAssignList)other).fNamedMapping;
		fParameters.clear();
		fParameters.addAll(((SVDBParamValueAssignList)other).fParameters);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBParamValueAssignList) {
			SVDBParamValueAssignList o = (SVDBParamValueAssignList)obj;
			
			if (o.fNamedMapping != fNamedMapping) {
				return false;
			}
			
			if (o.fParameters.size() == fParameters.size()) {
				for (int i=0; i<fParameters.size(); i++) {
					if (!fParameters.get(i).equals(o.fParameters.get(i))) {
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
