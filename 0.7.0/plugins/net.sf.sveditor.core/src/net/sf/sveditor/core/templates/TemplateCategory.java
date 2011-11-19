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


package net.sf.sveditor.core.templates;


public class TemplateCategory {
	private String							fId;
	private String							fName;
	
	public TemplateCategory(String id, String name) {
		fId = id;
		fName = name;
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}

}
