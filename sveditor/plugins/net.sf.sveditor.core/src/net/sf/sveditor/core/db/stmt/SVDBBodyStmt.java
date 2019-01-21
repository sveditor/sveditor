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


package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.utils.SVDBSingleItemIterable;

public abstract class SVDBBodyStmt extends SVDBStmt implements ISVDBBodyStmt, ISVDBAddChildItem, ISVDBChildParent {
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
