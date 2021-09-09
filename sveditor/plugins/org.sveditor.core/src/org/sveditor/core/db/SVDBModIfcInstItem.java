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


package org.sveditor.core.db;

import java.util.List;

import org.sveditor.core.db.stmt.SVDBVarDimItem;

public class SVDBModIfcInstItem extends SVDBItem implements ISVDBChildItem {
	public SVDBParamValueAssignList		fPortMap;
	public List<SVDBVarDimItem>			fArrayDim;
	
	
	public SVDBModIfcInstItem() {
		super("", SVDBItemType.ModIfcInstItem);
	}
	
	public SVDBModIfcInstItem(String name) {
		super(name, SVDBItemType.ModIfcInstItem);
	}
	
	public SVDBParamValueAssignList getPortMap() {
		return fPortMap;
	}
	
	public void setPortMap(SVDBParamValueAssignList map) {
		fPortMap = map;
	}
	
	public void setArrayDim(List<SVDBVarDimItem> dim) {
		fArrayDim = dim;
	}
	
	public List<SVDBVarDimItem> getArrayDim() {
		return fArrayDim;
	}

}
