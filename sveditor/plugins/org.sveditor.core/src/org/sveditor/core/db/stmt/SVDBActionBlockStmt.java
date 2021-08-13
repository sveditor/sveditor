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


package org.sveditor.core.db.stmt;

import org.sveditor.core.db.ISVDBAddChildItem;
import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.attr.SVDBDoNotSaveAttr;

public class SVDBActionBlockStmt extends SVDBStmt implements ISVDBAddChildItem {
	@SVDBDoNotSaveAttr
	private int						fAddIdx;
	
	public SVDBStmt					fStmt;
	public SVDBStmt					fElseStmt;
	
	public SVDBActionBlockStmt() {
		super(SVDBItemType.ActionBlockStmt);
	}
	
	public void setStmt(SVDBStmt stmt) {
		fStmt = stmt;
	}
	
	public SVDBStmt getStmt() {
		return fStmt;
	}
	
	public void setElseStmt(SVDBStmt stmt) {
		fElseStmt = stmt;
	}
	
	public SVDBStmt getElseStmt() {
		return fElseStmt;
	}

	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx++ == 0) {
			fStmt = (SVDBStmt)item;
		} else if (fAddIdx++ == 1) {
			fStmt = (SVDBStmt)item;
		}
	}

}
