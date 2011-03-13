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

public class SVDBParamValueAssignList extends SVDBItem {
	
	private boolean							fNamedMapping;
	private List<SVDBParamValueAssign>		fParameters;
	
	public SVDBParamValueAssignList() {
		super("", SVDBItemType.ParamValueAssignList);
		fNamedMapping = false;
		fParameters = new ArrayList<SVDBParamValueAssign>();
	}

	public List<SVDBParamValueAssign> getParameters() {
		return fParameters;
	}
	
	public void addParameter(SVDBParamValueAssign assign) {
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
		SVDBParamValueAssignList ret = new SVDBParamValueAssignList();
		
		ret.init(this);
		
		return ret;
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
