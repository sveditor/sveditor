/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import org.eclipse.hdt.sveditor.core.db.expr.SVDBIdentifierExpr;

public class SVDBParamValueAssignList extends SVDBItem implements ISVDBEndLocation {
	
	public boolean							fNamedMapping;
	public List<SVDBParamValueAssign>		fParameters;
	public long								fEndLocation;
	
	public SVDBParamValueAssignList() {
		super("", SVDBItemType.ParamValueAssignList);
		fNamedMapping = false;
		fParameters = new ArrayList<SVDBParamValueAssign>();
	}
	
	public void setEndLocation(long l) {
		fEndLocation = l;
	}
	
	public long getEndLocation() {
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
