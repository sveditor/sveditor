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

package net.sf.sveditor.core.docs;

import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.docs.model.DocTopic;

public interface IDocCommentParser {
	
	enum CommentType {
		DocComment,
		TaskTag,
		None
	}

	/**
	 * Returns a tuple <tag,title>
	 * @param comment
	 * @return
	 */
	public CommentType isDocCommentOrTaskTag(String comment, Tuple<String, String> info) ;
	
	public void parse(String comment, List<DocTopic> docTopics) ;
	
	public int parseComment(String lines[], List<DocTopic> parsedTopics) ;
		
}
