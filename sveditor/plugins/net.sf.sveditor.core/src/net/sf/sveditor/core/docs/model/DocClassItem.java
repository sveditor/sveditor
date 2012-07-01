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

import java.util.ArrayList;

public class DocClassItem extends DocItem {
	ArrayList<DocTopic> fTopics ;
	private String fShortDescription ;
	public ArrayList<DocTopic> getTopics() {
		return fTopics ;
	}
	public String getShortDescription() {
		return fShortDescription;
	}
	public void setShortDescription(String shortDescription) {
		this.fShortDescription = shortDescription;
	}
	public void addTopic(DocTopic topic) {
		fTopics.add(topic) ;
	}
	public DocClassItem(String name) {
		super(name, DocItemType.ClassDoc) ;
		fTopics = new ArrayList<DocTopic>() ;
		fShortDescription = "Sort description of class" ;
	}
}
