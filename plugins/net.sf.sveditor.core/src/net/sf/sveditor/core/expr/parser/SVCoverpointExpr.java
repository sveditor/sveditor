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


package net.sf.sveditor.core.expr.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SVCoverpointExpr extends SVCoverageExpr {
	private Map<String, String>		fOptionMap;
	private Map<String, String>		fTypeOptionMap;
	private List<SVCoverBinsExpr>	fCoverBins;
	private SVExpr					fIffExpr;
	private SVExpr					fTarget;

	public SVCoverpointExpr() {
		super(SVExprType.Coverpoint);
		
		fOptionMap  	= new HashMap<String, String>();
		fTypeOptionMap 	= new HashMap<String, String>();
		fCoverBins 		= new ArrayList<SVCoverBinsExpr>();
	}
	
	public List<SVCoverBinsExpr> getCoverBins() {
		return fCoverBins;
	}
	
	public SVExpr getTarget() {
		return fTarget;
	}
	
	public void setTarget(SVExpr target) {
		fTarget = target;
	}
	
	public SVExpr getIFFExpr() {
		return fIffExpr;
	}
	
	public void setIFFExpr(SVExpr iff_expr) {
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

}
