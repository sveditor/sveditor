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


package net.sf.sveditor.core.fileset;

import java.util.ArrayList;
import java.util.List;

public class SVFileSet {
	
	protected String						fBaseLocation;
	protected List<String>					fIncludes;
	protected List<String>					fExcludes;
	
	
	public SVFileSet(String base_location) {
		fBaseLocation = base_location;
		
		fIncludes 			= new ArrayList<String>();
		fExcludes 			= new ArrayList<String>();
	}
	
	public String getBase() {
		return fBaseLocation;
	}
	
	
	public void addInclude(String inc) {
		fIncludes.add(inc);
	}
	
	public void addExclude(String exc) {
		fExcludes.add(exc);
	}
	
	public List<String> getIncludes() {
		return fIncludes;
	}
	
	public List<String> getExcludes() {
		return fExcludes;
	}
	
}
