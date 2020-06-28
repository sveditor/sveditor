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


package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.SVDBCovergroup.BinsKW;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCoverpointBins extends SVDBItem {
	public enum BinsType {
		OpenRangeList,
		TransList,
		Default,
		DefaultSeq
	};
	
	
	public boolean					fWildcard;
	public BinsKW					fBinsKW;
	public BinsType				fBinsType;
	public boolean					fIsArray;
	public SVDBExpr				fArrayExpr;
	public SVDBExpr				fIFF;
	public SVDBExpr				fWith;
	
//	private List<SVDBExpr>			fRangeList;
	
	public SVDBCoverpointBins() {
		super("", SVDBItemType.CoverpointBins);
	}
	
	public SVDBCoverpointBins(boolean wildcard, String name, BinsKW kw) {
		super(name, SVDBItemType.CoverpointBins);
		fWildcard = wildcard;
		fBinsKW = kw;
	}
	
	public void setIsWildcard(boolean wildcard) {
		fWildcard = wildcard;
	}
	
	public boolean isWildcard() {
		return fWildcard;
	}
	
	public BinsKW getBinsKW() {
		return fBinsKW;
	}
	
	public void setBinsKW(BinsKW kw) {
		fBinsKW = kw;
	}
	
	public void setIsArray(boolean is_array) {
		fIsArray = is_array;
	}
	
	public boolean isArray() {
		return fIsArray;
	}
	
	public SVDBExpr getArrayExpr() {
		return fArrayExpr;
	}
	
	public void setArrayExpr(SVDBExpr expr) {
		fArrayExpr = expr;
	}
	
	public void setBinsType(BinsType type) {
		fBinsType = type;
	}
	
	public BinsType getBinsType() {
		return fBinsType;
	}
	
	public SVDBExpr getIFF() {
		return fIFF;
	}
	
	public void setIFF(SVDBExpr expr) {
		fIFF = expr;
	}
	
	public SVDBExpr getWith() {
		return fWith;
	}
	
	public void setWith(SVDBExpr expr) {
		fWith = expr;
	}
	
}
