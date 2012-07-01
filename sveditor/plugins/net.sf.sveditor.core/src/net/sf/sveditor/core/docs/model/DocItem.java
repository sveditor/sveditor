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

package net.sf.sveditor.core.docs.model;

import java.util.HashSet;
import java.util.Set;

public class DocItem implements IDocItem {
	
	private DocItemType fItemType ;
	private String fName ;
	private Set<DocItem> fChildren ;
	private String fSummary ; 
	
	public DocItem(String name, DocItemType type, String summary) {
		fName = name ;
		fItemType = type ;
		fChildren = new HashSet<DocItem>() ;
		fSummary = summary ;
	}

	public String getName() {
		return fName;
	}
	
	public void addChild(DocItem child) {
		fChildren.add(child) ;
	}
	
	public Set<DocItem> getChildren() {
		return fChildren ;
	}

	public void setName(String name) {
		this.fName = name;
	}

	public DocItemType getType() {
		return fItemType;
	}

	public void setItemType(DocItemType itemType) {
		this.fItemType = itemType;
	}
	
	public String getSummary() {
		return fSummary ;
	}
	public void setSummary(String summary) {
		this.fSummary = summary ;
	}

}
