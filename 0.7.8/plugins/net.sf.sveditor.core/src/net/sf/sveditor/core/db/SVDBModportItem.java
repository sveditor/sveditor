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

public class SVDBModportItem extends SVDBItem {
	List<SVDBModportPortsDecl>		fPorts;
	
	public SVDBModportItem() {
		this("");
	}
	
	public SVDBModportItem(String name) {
		super(name, SVDBItemType.ModportItem);
		fPorts = new ArrayList<SVDBModportPortsDecl>();
	}
	
	public List<SVDBModportPortsDecl> getPortsList() {
		return fPorts;
	}
	
	public void addPorts(SVDBModportPortsDecl p) {
		fPorts.add(p);
	}

}
