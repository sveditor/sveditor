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


package org.eclipse.hdt.sveditor.core.db.stmt;

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import org.eclipse.hdt.sveditor.core.db.utils.SVDBSingleItemIterable;

public class SVDBBodyStmt extends SVDBStmt implements ISVDBBodyStmt, ISVDBAddChildItem, ISVDBChildParent {
	public SVDBStmt			fBody;
	
	@SVDBDoNotSaveAttr
	private int					fAddIdx;
	
	protected SVDBBodyStmt(SVDBItemType stmt_type) {
		super(stmt_type);
	}
	
	public void setBody(SVDBStmt stmt) {
		fBody = stmt;
	}
	
	public SVDBStmt getBody() {
		return fBody;
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return new SVDBSingleItemIterable<ISVDBChildItem>(fBody);
	}

	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx++ == 0) {
			fBody = (SVDBStmt)item;
			if (fBody != null) {
				fBody.setParent(this);
			}
		}
	}

}
