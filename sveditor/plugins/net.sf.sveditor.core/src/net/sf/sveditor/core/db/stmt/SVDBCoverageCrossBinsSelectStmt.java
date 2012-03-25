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

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCoverageCrossBinsSelectStmt extends SVDBStmt {
	public SVDBCoverageBinsType	fBinsType;
	public SVDBExpr				fBinsName;
	public SVDBExpr				fSelectCondition;
	public SVDBExpr				fIffExpr;
	
	public SVDBCoverageCrossBinsSelectStmt() {
		super(SVDBItemType.CoverageCrossBinsSelectStmt);
	}
	
	public SVDBCoverageBinsType getBinsType() {
		return fBinsType;
	}
	
	public void setBinsType(SVDBCoverageBinsType type) {
		fBinsType = type;
	}
	
	public void setBinsType(String type) {
		if (type.equals("ignore_bins")) {
			fBinsType = SVDBCoverageBinsType.IgnoreBins;
		} else if (type.equals("illegal_bins")) {
			fBinsType = SVDBCoverageBinsType.IllegalBins;
		} else {
 			fBinsType = SVDBCoverageBinsType.Bins; 
		}
	}
	
	public SVDBExpr getBinsName() {
		return fBinsName;
	}
	
	public void setBinsName(SVDBExpr name) {
		fBinsName = name;
	}
	
	public SVDBExpr getSelectCondition() {
		return fSelectCondition;
	}
	
	public void setSelectCondition(SVDBExpr expr) {
		fSelectCondition = expr;
	}
	
	public SVDBExpr getIffExpr() {
		return fIffExpr;
	}
	
	public void setIffExpr(SVDBExpr iff) {
		fIffExpr = iff;
	}

}
