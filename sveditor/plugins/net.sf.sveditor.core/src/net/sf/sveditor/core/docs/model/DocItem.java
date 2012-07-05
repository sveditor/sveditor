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
	
	// FIXME: rename this class to DocTopic
	
	private DocItemType fItemType ;
	private String fName ; // FIXME: change to fTitle
	private String fSummary ; 
	private String fBody ;
	private Set<DocItem> fChildren ;
	private String fEnclosingPkg ; 
	private String fEnclosingClass ; 
	private DocFile fDocFile ;
	
	public DocItem(String name, DocItemType type) {
		fName = name ;
		fItemType = type ;
		fChildren = new HashSet<DocItem>() ;
		fSummary = "" ;
		fBody = "" ;
		fEnclosingPkg = "" ;
		fEnclosingClass = "" ;
		fDocFile = null ;
	}

	public String getName() { // FIXME: remove
		return fName;
	}
	
	public String getQualifiedName() {
		String ret = fName ;
		if(!fEnclosingClass.isEmpty()) {
			ret = fEnclosingClass + "::" + ret ;
		}
		if(!fEnclosingPkg.isEmpty()) {
			ret = fEnclosingPkg + "::" + ret ;
		}
		return ret ;
	}
	
	public String getTitle() {
		return fName;
	}
	
	public void setTitle(String title) {
		fName = title ;
	}
	
	public void addChild(DocItem child) {
		fChildren.add(child) ;
		child.setDocFile(getDocFile()) ;
	}
	
	public Set<DocItem> getChildren() {
		return fChildren ;
	}

	public void setName(String name) { // FIXME: remove
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

	public void setBody(String body) {
		this.fBody = body;
	}
	public String getBody() {
		return fBody ;
	}

	public String getEnclosingPkg() {
		return fEnclosingPkg;
	}

	public void setEnclosingPkg(String pkg) {
		this.fEnclosingPkg = pkg;
	}

	public String getEnclosingClass() {
		return fEnclosingClass;
	}

	public void setEnclosingClass(String c) {
		this.fEnclosingClass = c ;
	}
	
	public DocFile getDocFile() {
		return fDocFile;
	}

	public void setDocFile(DocFile docFile) {
		this.fDocFile = docFile;
	}


}