/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs.model;

import java.util.ArrayList;
import java.util.List;

public class DocTopic implements IDocTopic {
	
	private String fTitle ; 
	private String fSummary ; 
	private String fKeyword ;
	
	private String fTopic ; 
	private String fBody ;
	private List<DocTopic> fChildren ;
	private String fEnclosingPkg ; 
	private String fEnclosingClass ; 
	private DocFile fDocFile ;
	
	public DocTopic() {
		fTitle = "" ;
		fChildren = new ArrayList<DocTopic>() ;
		fSummary = "" ;
		fBody = "" ;
		fEnclosingPkg = "" ;
		fEnclosingClass = "" ;
		fDocFile = null ;
	}

	public DocTopic(String topicTitle, String topicTypeName, String keyword) {
		this() ;
		setTitle(topicTitle) ;
		setTopic(topicTypeName) ;
		setKeyword(keyword) ;
	}

	public String getQualifiedName() {
		String ret = fTitle ;
		if(!fEnclosingClass.isEmpty()) {
			ret = fEnclosingClass + "::" + ret ;
		}
		if(!fEnclosingPkg.isEmpty()) {
			ret = fEnclosingPkg + "::" + ret ;
		}
		return ret ;
	}
	
	public String getTitle() {
		return fTitle;
	}
	
	public void setTitle(String title) {
		fTitle = title ;
	}
	
	public void addChild(DocTopic child) {
		fChildren.add(child) ;
		child.setDocFile(getDocFile()) ;
	}
	
	public List<DocTopic> getChildren() {
		return fChildren ;
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
	public String getKeyword() {
		return fKeyword;
	}

	public void setKeyword(String keyword) {
		this.fKeyword = keyword;
	}

	public String getTopic() {
		return fTopic ;
	}

	public void setTopic(String topic) {
		this.fTopic = topic;
	}
	
	private int fFieldAttr ;

	public void setAttr(int attr) {
		fFieldAttr = attr ;
	}

	public int getAttr() {
		return fFieldAttr ;
	}


}