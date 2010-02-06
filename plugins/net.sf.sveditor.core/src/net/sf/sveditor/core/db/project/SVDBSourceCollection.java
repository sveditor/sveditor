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


package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

public class SVDBSourceCollection {
	private String					fBaseLocation;
	private List<String>			fIncludes;
	private List<String>			fExcludes;
	
	public SVDBSourceCollection(String base_location) {
		fBaseLocation = base_location;
		fIncludes = new ArrayList<String>();
		fExcludes = new ArrayList<String>();
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public void setBaseLocation(String base) {
		fBaseLocation = base;
	}
	
	public List<String> getIncludes() {
		return fIncludes;
	}
	
	public String getIncludesStr() {
		String ret = "";
		
		for (int i=0; i<fIncludes.size(); i++) {
			ret += fIncludes.get(i);
			if (i+1 < fIncludes.size()) {
				ret += ", ";
			}
		}
		
		return ret;
	}
	
	public List<String> getExcludes() {
		return fExcludes;
	}

	public String getExcludesStr() {
		String ret = "";
		
		for (int i=0; i<fExcludes.size(); i++) {
			ret += fExcludes.get(i);
			if (i+1 < fExcludes.size()) {
				ret += ", ";
			}
		}
		
		return ret;
	}

	public SVDBSourceCollection duplicate() {
		SVDBSourceCollection ret = new SVDBSourceCollection(fBaseLocation);
		
		ret.getIncludes().addAll(fIncludes);
		ret.getExcludes().addAll(fExcludes);
		
		return ret;
	}
	
	public static List<String> parsePatternList(String pattern) {
		String arr[] = pattern.split(",");
		List<String> ret = new ArrayList<String>();
		
		for (String p : arr) {
			ret.add(p.trim());
		}
		
		return ret;
	}
}
