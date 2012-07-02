/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs ;


class DocTopicType {
	
	enum ScopeType { NORMAL, START, END, ALWAYS_GLOBAL } ;
	
	private String name ;
	private String pluralName ;
	private boolean index ;
	private boolean pageTitleIfFirst ;
	private boolean breakLists ;
	
	public DocTopicType(String name, String pluralName, boolean index, boolean pageTitleIfFirst, boolean breakLists) {
		this.name = name ;
		this.pluralName = pluralName ;
		this.index = index ;
		this.pageTitleIfFirst = pageTitleIfFirst ;
		this.breakLists = breakLists ;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getPluralName() {
		return pluralName;
	}

	public void setPluralName(String pluralName) {
		this.pluralName = pluralName;
	}

	public boolean isIndex() {
		return index;
	}

	public void setIndex(boolean index) {
		this.index = index;
	}

	public boolean isPageTitleIfFirst() {
		return pageTitleIfFirst;
	}

	public void setPageTitleIfFirst(boolean pageTitleIfFirst) {
		this.pageTitleIfFirst = pageTitleIfFirst;
	}

	public boolean isBreakLists() {
		return breakLists;
	}

	public void setBreakLists(boolean breakLists) {
		this.breakLists = breakLists;
	}
	
	
}