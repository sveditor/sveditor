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


package org.sveditor.core.db;

import org.sveditor.core.db.expr.SVDBExpr;
import org.sveditor.core.db.expr.SVDBIdentifierExpr;

public class SVDBCoverCrossBinsSel extends SVDBItem {
	
	public SVDBExpr				fSelectExpr;
	
	public SVDBCoverCrossBinsSel() {
		super("", SVDBItemType.CoverCrossBinsSel);
	}
	
	public SVDBCoverCrossBinsSel(SVDBIdentifierExpr id) {
		super(id, SVDBItemType.CoverCrossBinsSel);
	}
	
	public void setSelectExpr(SVDBExpr expr) {
		fSelectExpr = expr;
	}
	
	public SVDBExpr getSelectExpr() {
		return fSelectExpr;
	}

}
