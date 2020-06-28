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


package net.sf.sveditor.core.db.project;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;

public class SVDBSourceCollection {
	private String					fBaseLocation;
	private List<String>			fIncludes;
	private List<String>			fExcludes;
	private boolean					fDefaultIncExcl;
	
	public SVDBSourceCollection(String base_location, boolean dflt_inc_excl) {
		fBaseLocation = base_location;
		fIncludes = new ArrayList<String>();
		fExcludes = new ArrayList<String>();
		setDefaultIncExcl(dflt_inc_excl);
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public boolean getDefaultIncExcl() {
		return fDefaultIncExcl;
	}
	
	public void setDefaultIncExcl(boolean dflt_inc_excl) {
		if (fDefaultIncExcl != dflt_inc_excl) {
			if (dflt_inc_excl) {
				fIncludes.clear();
				fExcludes.clear();
				
				fIncludes.addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes()));
				fExcludes.addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes()));
			}
		}
		fDefaultIncExcl = dflt_inc_excl;
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
		SVDBSourceCollection ret = new SVDBSourceCollection(fBaseLocation, getDefaultIncExcl());

		if (!getDefaultIncExcl()) {
			ret.getIncludes().addAll(fIncludes);
			ret.getExcludes().addAll(fExcludes);
		}
		
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
