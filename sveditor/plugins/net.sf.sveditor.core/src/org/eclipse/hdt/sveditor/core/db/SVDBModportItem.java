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

public class SVDBModportItem extends SVDBItem {
	public List<SVDBModportPortsDecl>		fPorts;
	
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
