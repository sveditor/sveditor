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

public class SVTaskFuncParam {
	
	private String					fName;
	private String					fTypeName;
	
	public SVTaskFuncParam(String type, String name) {
		fTypeName = type;
		fName     = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getTypeName() {
		return fTypeName;
	}
}
