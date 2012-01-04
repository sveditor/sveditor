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

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCoverBinsExpr extends SVCoverageExpr {
	String				fName;
	String				fBinsType;
	boolean				fIsArray;
	SVDBExpr			fArrayExpr;
	List<SVDBExpr>		fRangeList;
	boolean				fIsDefault;
	
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
