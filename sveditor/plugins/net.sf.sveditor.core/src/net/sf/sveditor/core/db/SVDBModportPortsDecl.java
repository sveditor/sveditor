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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBModportPortsDecl extends SVDBChildItem implements ISVDBAddChildItem {
	public List<ISVDBChildItem>			fPorts;
	
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
