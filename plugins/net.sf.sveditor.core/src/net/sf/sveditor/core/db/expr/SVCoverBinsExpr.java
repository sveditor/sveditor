/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

public class SVCoverBinsExpr extends SVCoverageExpr {
	private String				fName;
	private String				fBinsType;
	private boolean				fIsArray;
	private SVExpr				fArrayExpr;
	private List<SVExpr>		fRangeList;
	private boolean				fIsDefault;
	
	public SVCoverBinsExpr(String name, String bins_type) {
		super(SVExprType.CoverBins);
		fName 			= name;
		fBinsType 		= bins_type;
		fRangeList  	= new ArrayList<SVExpr>();
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
	
	public SVExpr getArrayExpr() {
		return fArrayExpr;
	}
	
	public void setArrayExpr(SVExpr expr) {
		fArrayExpr = expr;
	}
	
	public List<SVExpr> getRangeList() {
		return fRangeList;
	}
	
	public SVCoverBinsExpr duplicate() {
		SVCoverBinsExpr ret = new SVCoverBinsExpr(fName, fBinsType);
		ret.fIsArray = fIsArray;
		ret.fArrayExpr = (SVExpr)((fArrayExpr != null)?fArrayExpr.duplicate():null);
		for (SVExpr e : fRangeList) {
			ret.fRangeList.add((SVExpr)e.duplicate());
		}
		ret.fIsDefault = fIsDefault;
		
		return ret;
	}
	

}
