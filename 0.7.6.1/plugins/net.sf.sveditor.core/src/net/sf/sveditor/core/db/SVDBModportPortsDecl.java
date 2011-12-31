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

public class SVDBModportPortsDecl extends SVDBChildItem implements ISVDBAddChildItem {
	private List<ISVDBChildItem>			fPorts;
	
	protected SVDBModportPortsDecl(SVDBItemType type) {
		super(type);
		fPorts = new ArrayList<ISVDBChildItem>();
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fPorts.add(item);
	}
	
	public List<ISVDBChildItem> getPorts() {
		return fPorts;
	}
	
}
