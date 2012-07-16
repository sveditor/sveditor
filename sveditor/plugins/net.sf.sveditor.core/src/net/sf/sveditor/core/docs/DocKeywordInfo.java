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

package net.sf.sveditor.core.docs;

public class DocKeywordInfo {
	
	private String keyword ;
	private boolean isPlural ;
	private DocTopicType topicType ;
	
	public DocKeywordInfo(String keyword, DocTopicType topicType, boolean isPlural) {
		this.keyword = keyword ;
		this.topicType = topicType ;
		this.isPlural = isPlural ;
	}

	public String getKeyword() {
		return keyword;
	}

	public void setKeyword(String keyword) {
		this.keyword = keyword;
	}

	public boolean isPlural() {
		return isPlural;
	}

	public void setPlural(boolean isPlural) {
		this.isPlural = isPlural;
	}

	public DocTopicType getTopicType() {
		return topicType;
	}

	public void setTopicType(DocTopicType topicType) {
		this.topicType = topicType;
	}

}
