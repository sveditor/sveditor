/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.argfile.filter;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;

public class ArgFileFilterList implements IArgFileFilter {
	private List<IArgFileFilter>		fFilterList;
	
	public ArgFileFilterList() {
		fFilterList = new ArrayList<IArgFileFilter>();
	}
	
	public void addFilter(IArgFileFilter filter) {
		fFilterList.add(filter);
	}

	public SVDBFile filter(SVDBFile in) {
		for (IArgFileFilter f : fFilterList) {
			in = f.filter(in);
		}
		
		return in;
	}

}
