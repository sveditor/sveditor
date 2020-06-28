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
package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

public class SVDBRefCollectorVisitor implements ISVDBRefVisitor {
	
	private List<SVDBRefItem>				fItemList;
	
	public SVDBRefCollectorVisitor() {
		fItemList = new ArrayList<SVDBRefItem>(); 
	}
	
	public List<SVDBRefItem> getItemList() {
		return fItemList;
	}

	@Override
	public void visitRef(ISVDBRefSearchSpec ref_spec, SVDBRefItem item) {
		fItemList.add(item);
	}

	
}
