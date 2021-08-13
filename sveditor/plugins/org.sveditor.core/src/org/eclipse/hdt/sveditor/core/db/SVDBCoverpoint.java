/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

public class SVDBCoverpoint extends SVDBScopeItem {
	public SVDBExpr				fTarget;
	public SVDBExpr				fIFF;

	public SVDBCoverpoint() {
		super("", SVDBItemType.Coverpoint);
	}
	
	public SVDBCoverpoint(String name) {
		super(name, SVDBItemType.Coverpoint);
	}
	
	public SVDBExpr getTarget() {
		return fTarget;
	}
	
	public void setTarget(SVDBExpr expr) {
		fTarget = expr;
	}
	
	public SVDBExpr getIFF() {
		return fIFF;
	}
	
	public void setIFF(SVDBExpr expr) {
		fIFF = expr;
	}
	
	@Override
	public SVDBCoverpoint duplicate() {
		return (SVDBCoverpoint)SVDBItemUtils.duplicate(this);
	}

	@Override
	public void init(SVDBItemBase other) {
		SVDBCoverpoint other_i = (SVDBCoverpoint)other;
		
		super.init(other);
		
		fTarget = other_i.fTarget;
	}

/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBCoverpoint) {
			// TODO:
			return true;
		} else {
			return false;
		}
	}
 */
	
}
