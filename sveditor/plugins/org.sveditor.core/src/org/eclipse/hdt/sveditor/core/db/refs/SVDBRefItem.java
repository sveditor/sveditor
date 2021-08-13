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
package org.eclipse.hdt.sveditor.core.db.refs;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;

public class SVDBRefItem {
	private List<ISVDBItemBase>			fRefPath;
	private String						fRefName;
	private SVDBRefType					fRefType;
	
	public SVDBRefItem(
			List<ISVDBItemBase>			ref_path,
			String						ref_name,
			SVDBRefType					ref_type) {
		fRefPath = ref_path;
		fRefName = ref_name;
		fRefType = ref_type;
	}

	public SVDBFile getRoot() {
		return (SVDBFile)fRefPath.get(0);
	}
	
	public ISVDBItemBase getLeaf() {
		return fRefPath.get(fRefPath.size()-1);
	}

}
