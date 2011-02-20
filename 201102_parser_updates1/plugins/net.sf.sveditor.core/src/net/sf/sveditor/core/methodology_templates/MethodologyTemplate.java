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


package net.sf.sveditor.core.methodology_templates;

public class MethodologyTemplate {
	private String				fId;
	private String				fName;
	private String				fCategoryId;
	private String				fTemplate;
	
	public MethodologyTemplate(String id, String name, String category_id) {
		fId = id;
		fName = name;
		fCategoryId = (category_id != null)?category_id:"";
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getCategoryId() {
		return fCategoryId;
	}
	
	public String getTemplate() {
		return fTemplate;
	}
	
	public void setTemplate(String template) {
		fTemplate = template;
	}

}
