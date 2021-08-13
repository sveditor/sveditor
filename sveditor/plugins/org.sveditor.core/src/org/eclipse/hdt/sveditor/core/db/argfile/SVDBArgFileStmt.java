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
package org.sveditor.core.db.argfile;

import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.SVDBItemBase;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.attr.SVDBParentAttr;

public class SVDBArgFileStmt extends SVDBItemBase implements ISVDBChildItem {
	@SVDBParentAttr
	public ISVDBChildItem			fParent;
	
	public SVDBArgFileStmt(SVDBItemType type) {
		super(type);
	}

	public ISVDBChildItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

}
