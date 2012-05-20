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


public class TemplateCategory implements Comparable<TemplateCategory> {
	private String							fId;
	private String							fName;
	private String							fDescription;
	private String							fParent;
	
	public TemplateCategory(String id, String name, String parent) {
		fId = id;
		fName = name;
		fDescription = "";
		fParent = parent;
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getDescription() {
		return fDescription;
	}
	
	public void setDescription(String desc) {
		fDescription = desc;
	}
	
	public String getParent() {
		return fParent;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof TemplateCategory) {
			return fId.equals(((TemplateCategory)obj).fId);
		} else {
			return false;
		}
	}

	public int compareTo(TemplateCategory o) {
		return fName.compareTo(o.fName);
	}

}
