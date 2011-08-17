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

public class SVDBModIfcInstItem extends SVDBItem implements ISVDBChildItem {
	private SVDBParamValueAssignList		fPortMap;
	
	
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

}
