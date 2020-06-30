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


package org.eclipse.hdt.sveditor.core.db;

import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;

public class SVDBModportSimplePort extends SVDBChildItem implements ISVDBNamedItem {
	public boolean				fIsMapped;
	public String				fPortId;
	public SVDBExpr			fExpr;
	
	public SVDBModportSimplePort() {
		super(SVDBItemType.ModportSimplePort);
	}
	
	public void setIsMapped(boolean m) {
		fIsMapped = m;
	}
	
	public boolean isMapped() {
		return fIsMapped;
	}
	
	public void setPortId(String id) {
		fPortId = id;
	}
	
	public String getPortId() {
		return fPortId;
	}

	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

	public String getName() {
		return fPortId;
	}
}
