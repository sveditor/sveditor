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


package org.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.db.SVDBItemType;

public class SVDBCoverBinsExpr extends SVCoverageExpr {
	public String				fName;
	public String				fBinsType;
	public boolean				fIsArray;
	public SVDBExpr				fArrayExpr;
	public List<SVDBExpr>		fRangeList;
	public boolean				fIsDefault;
	
	public SVDBCoverBinsExpr() {
		this(null, null);
	}
	
	public SVDBCoverBinsExpr(String name, String bins_type) {
		super(SVDBItemType.CoverBinsExpr);
		fName 			= name;
		fBinsType 		= bins_type;
		fRangeList  	= new ArrayList<SVDBExpr>();
	}
	
	public String getName() {
		return fName;
	}
	
	public void setIsDefault(boolean dflt) {
		fIsDefault = dflt;
	}
	
	public boolean isDefault() {
		return fIsDefault;
	}
	
	public String getBinsType() {
		return fBinsType;
	}
	
	public boolean isArray() {
		return fIsArray;
	}
	
	public void setIsArray(boolean is_array) {
		fIsArray = is_array;
	}
	
	public SVDBExpr getArrayExpr() {
		return fArrayExpr;
	}
	
	public void setArrayExpr(SVDBExpr expr) {
		fArrayExpr = expr;
	}
	
	public List<SVDBExpr> getRangeList() {
		return fRangeList;
	}
	
	public SVDBCoverBinsExpr duplicate() {
		return (SVDBCoverBinsExpr)super.duplicate();
	}
	

}
