/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - Initial contributor 
 *     
 *****************************************************************************/

package net.sf.sveditor.core.docs.model;


// Temporarily storing the Topic parsed from the comments 
// as a DocItem.  Not sure if this makes sense but in the long run.
// Will see how it works when trying to merge the parsed comments 
// into the DocModel

public class DocTopic extends DocItem {
	
//	String topicType ;
	String title ;
	String body ;

	public DocTopic(String name, DocItemType type, String body, String title) {
		super(name, type) ;
		this.body = body ;
		this.title = title ;
	}

	public String getTitle() {
		return title;
	}

	public void setTitle(String title) {
		this.title = title;
	}

	public String getBody() {
		return body;
	}

	public void setBody(String body) {
		this.body = body;
	}

}
