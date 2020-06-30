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

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;

public class SVDBCovergroup extends SVDBModIfcDecl {
	public enum BinsKW {
		Bins,
		IllegalBins,
		IgnoreBins
	};
	
	public SVDBExpr				fCoverageEventExpr;
	public List<SVDBParamPortDecl>	fParamPort;

	public SVDBCovergroup() {
		super("", SVDBItemType.Covergroup);
	}
	
	public SVDBCovergroup(String name) {
		super(name, SVDBItemType.Covergroup);
	}
	
	public void setParamPort(List<SVDBParamPortDecl> params) {
		fParamPort = params;
	}
	
	public List<SVDBParamPortDecl> getParamPort() {
		return fParamPort;
	}
	
	public void setCoverageEvent(SVDBExpr expr) {
		fCoverageEventExpr = expr;
	}
	
	public SVDBExpr getCoverageEvent() {
		return fCoverageEventExpr;
	}
	
	public SVDBCovergroup duplicate() {
		return (SVDBCovergroup)SVDBItemUtils.duplicate(this);
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
	}
	
}
