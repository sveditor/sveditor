/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package org.sveditor.core.docs;

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
