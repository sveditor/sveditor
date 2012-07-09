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


public class DocTopicType {
	
	
	// Scope: [normal|start|end|always global]
	//    How the topics affects scope.  Defaults to normal.
	//    normal        - Topics stay within the current scope.
	//    start         - Topics start a new scope for all the topics beneath it,
	//                    like class topics.
	//    end           - Topics reset the scope back to global for all the topics
	//                    beneath it.
	//    always global - Topics are defined as global, but do not change the scope
	//                    for any other topics.
	
	public enum ScopeType { NORMAL, START, END, ALWAYS_GLOBAL } ;
	
	private String name ;
	private String pluralName ;
	private boolean index ;
	private boolean pageTitleIfFirst ;
	private boolean breakLists ;
	private ScopeType scopeType ;
	
	public DocTopicType(String name, String pluralName, ScopeType scopeType, boolean index, boolean pageTitleIfFirst, boolean breakLists) {
		this.name = name ;
		this.pluralName = pluralName ;
		this.scopeType = scopeType ;
		this.index = index ;
		this.pageTitleIfFirst = pageTitleIfFirst ;
		this.breakLists = breakLists ;
	}

	public String getName() {
		return name;
	}
	
	public String getNameCapitalized() {
		return name.substring(0,1).toUpperCase() + name.substring(1).toLowerCase() ;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getPluralName() {
		return pluralName;
	}
	
	public String getPluralNameCapitalized() {
		return pluralName.substring(0,1).toUpperCase() + pluralName.substring(1).toLowerCase() ;
	}
	
	public ScopeType getScopeType() {
		return scopeType ;
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