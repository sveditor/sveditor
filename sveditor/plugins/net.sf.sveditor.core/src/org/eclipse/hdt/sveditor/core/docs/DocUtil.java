/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.docs;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBDocComment;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindDocComment;
import org.eclipse.hdt.sveditor.core.docs.html.HTMLFromNDMarkup;
import org.eclipse.hdt.sveditor.core.docs.model.DocTopic;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class DocUtil {
	
	private static final LogHandle				fLog = LogFactory.getLogHandle("DocUtil");
	
	
	public static String getDocComment(
			ISVDBIndexIterator			index_it,
			ISVDBItemBase				element) {
		StringBuffer buffer = new StringBuffer();
		
		if(!(element instanceof ISVDBNamedItem )) {
			return null ;
		}		

		SVDBFindDocComment finder = new SVDBFindDocComment(index_it);
		SVDBDocComment docCom = finder.find(new NullProgressMonitor(), element);

		if(docCom == null) {
			fLog.debug(ILogLevel.LEVEL_MID,
				String.format("Did not find doc comment for(%s)", SVDBItem.getName(element)));
			return null ;
		}
		
		List<DocTopic> docTopics = new ArrayList<DocTopic>() ;
		
		IDocTopicManager topicMgr = new DocTopicManager() ;
		
		IDocCommentParser docCommentParser = new DocCommentParser(topicMgr) ;
		
		fLog.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, 
				"| Raw Comment") ;
		fLog.debug(ILogLevel.LEVEL_MID,
				"| " + docCom.getRawComment()) ;
		fLog.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;
			
		docCommentParser.parse(docCom.getRawComment(), docTopics) ;
		
		buffer.append(genContent(docTopics)) ;

		if (buffer.length() > 0) {
			return buffer.toString();
		} else {
			return null;
		}
	}
	
	private static String genContent(List<DocTopic> topics) {
		String res = "" ;
		HTMLFromNDMarkup markupConverter = new HTMLFromNDMarkup() ;
		for(DocTopic topic: topics) {
			String html = "" ;
			html = genContentForTopic(topic) ;
			html = markupConverter.convertNDMarkupToHTML(null, topic, html, HTMLFromNDMarkup.NDMarkupToHTMLStyle.Tooltip) ;
			res += html ;
		}
		return res ;
	}		
	
	private static String genContentForTopic(DocTopic topic) {
		String res = "" ;
		res += "<h4>" ;
		res += topic.getTitle() ;
		res += "</h4>" ;
		res += topic.getBody() ;
		for(DocTopic childTopic: topic.getChildren()) {
			res += genContentForTopic(childTopic) ;
		}
		return res ;
	}	
}
