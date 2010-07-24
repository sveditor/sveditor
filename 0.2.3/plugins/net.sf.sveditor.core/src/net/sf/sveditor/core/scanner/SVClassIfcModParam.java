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


package net.sf.sveditor.core.scanner;

public class SVClassIfcModParam {
	private String				fName;
	private String				fDefault;
	
	
	public SVClassIfcModParam(String name) {
		fName = name;
		fDefault = "";
	}

	public String getName() {
		return fName;
	}

	public void setDefault(String dflt) {
		fDefault = dflt;
	}
	
	public String getDefault() {
		return fDefault;
	}
}
