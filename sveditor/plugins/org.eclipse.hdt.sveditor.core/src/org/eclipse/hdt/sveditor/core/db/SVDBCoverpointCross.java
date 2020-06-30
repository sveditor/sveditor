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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBIdentifierExpr;

public class SVDBCoverpointCross extends SVDBScopeItem {
	public List<SVDBIdentifierExpr>	fCoverpointList;
	public SVDBExpr					fIFF;

	public SVDBCoverpointCross() {
		super("", SVDBItemType.CoverpointCross);
	}

	public SVDBCoverpointCross(String name) {
		super(name, SVDBItemType.CoverpointCross);
		fCoverpointList = new ArrayList<SVDBIdentifierExpr>();
	}
	
	public SVDBExpr getIFF() {
		return fIFF;
	}
	
	public void setIFF(SVDBExpr expr) {
		fIFF = expr;
	}

	public List<SVDBIdentifierExpr> getCoverpointList() {
		return fCoverpointList;
	}
	
	@Override
	public SVDBItemBase duplicate() {
		return (SVDBCoverpointCross)SVDBItemUtils.duplicate(this);
	}

	@Override
	public void init(SVDBItemBase other) {
		SVDBCoverpointCross other_i = (SVDBCoverpointCross)other;
		
		super.init(other);
		
		fCoverpointList.clear();
		fCoverpointList.addAll(other_i.fCoverpointList);
	}


	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBCoverpointCross) {
			SVDBCoverpointCross o = (SVDBCoverpointCross)obj;
			if (o.fCoverpointList.size() == fCoverpointList.size()) {
				for (int i=0; i<fCoverpointList.size(); i++) {
					if (!o.fCoverpointList.get(i).equals(fCoverpointList.get(i))) {
						return false;
					}
				}
			}
			return super.equals(obj);
		}
		
		return false;
	}
	 */

}
