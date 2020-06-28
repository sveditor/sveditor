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


package org.eclipse.hdt.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBCoverpointExpr extends SVCoverageExpr {
	public Map<String, String>		fOptionMap;
	public Map<String, String>		fTypeOptionMap;
	public List<SVDBCoverBinsExpr>	fCoverBins;
	public SVDBExpr					fIffExpr;
	public SVDBExpr					fTarget;

	public SVDBCoverpointExpr() {
		super(SVDBItemType.CoverpointExpr);
		
		fOptionMap  	= new HashMap<String, String>();
		fTypeOptionMap 	= new HashMap<String, String>();
		fCoverBins 		= new ArrayList<SVDBCoverBinsExpr>();
	}
	
	public List<SVDBCoverBinsExpr> getCoverBins() {
		return fCoverBins;
	}
	
	public SVDBExpr getTarget() {
		return fTarget;
	}
	
	public void setTarget(SVDBExpr target) {
		fTarget = target;
	}
	
	public SVDBExpr getIFFExpr() {
		return fIffExpr;
	}
	
	public void setIFFExpr(SVDBExpr iff_expr) {
		fIffExpr = iff_expr;
	}

	public void addOption(String key, String value) {
		if (fOptionMap.containsKey(key)) {
			fOptionMap.remove(key);
		}
		fOptionMap.put(key, value);
	}

	public void addTypeOption(String key, String value) {
		if (fTypeOptionMap.containsKey(key)) {
			fTypeOptionMap.remove(key);
		}
		fTypeOptionMap.put(key, value);
	}

	public Map<String, String> getOptionMap() {
		return fOptionMap;
	}
	
	public Map<String, String> getTypeOptionMap() {
		return fTypeOptionMap;
	}
	
	public SVDBCoverpointExpr duplicate() {
		return (SVDBCoverpointExpr)super.duplicate();
	}

}
