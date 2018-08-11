/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;

import java.util.List;

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;

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
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_covergroup(this);
	}
	
}
