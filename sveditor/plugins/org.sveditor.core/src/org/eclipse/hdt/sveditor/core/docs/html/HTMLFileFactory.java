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

package org.eclipse.hdt.sveditor.core.docs.html;

import java.io.File;

import org.eclipse.hdt.sveditor.core.docs.DocGenConfig;
import org.eclipse.hdt.sveditor.core.docs.model.DocFile;
import org.eclipse.hdt.sveditor.core.docs.model.DocModel;
import org.eclipse.hdt.sveditor.core.docs.model.DocTopic;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class HTMLFileFactory {
	
	private DocGenConfig cfg ;
	private DocModel model ;
	@SuppressWarnings("unused")
	private LogHandle fLog ;
	private HTMLFromNDMarkup fMarkupToHTML ;
	
	public HTMLFileFactory(DocGenConfig cfg, DocModel model) {
		this.cfg = cfg ;
		this.model = model ;
		fLog = LogFactory.getLogHandle("HTMLFileFactory") ;
		fMarkupToHTML = new HTMLFromNDMarkup(this.model) ;
	}
	
	public static String getRelPathToHTML(String path) {
		String res = "" ;
		File filePath = new File(path) ;
		int numParents=0 ;
		while(filePath.getParentFile() != null) {
			numParents++ ;
			filePath = filePath.getParentFile() ;  
		}
		for(int i=0 ; i<numParents ; i++) {
			res += "../" ;
		}
		return res ;
	}
	
	public String build(DocFile docFile) {
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart(getRelPathToHTML(docFile.getTitle()),docFile.getPageTitle()) ;
		res += HTMLUtils.genBodyBegin("ContentPage") ;
		res += HTMLUtils.genContentBegin() ;
		res += genContent(docFile) ;
		res += HTMLUtils.genContentEnd() ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu(
					cfg, 
					getRelPathToHTML(docFile.getTitle()),
					docFile.getPageTitle(),
					model.getDocTopics().getAllTopicTypes()) ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genSummaryStart(DocFile docFile, DocTopic docItem) {
		String result = "" ;
		result += fMarkupToHTML.convertNDMarkupToHTML(docFile, docItem, docItem.getBody(),HTMLFromNDMarkup.NDMarkupToHTMLStyle.General) ;
		return result ;
	}

	private String genMemberDetail(DocFile docFile, DocTopic docTopic) {
		String res = "" ;
		for(DocTopic child: docTopic.getChildren()) {
			res += genDetails(docFile, docTopic, child) ;
		}
		return res ;
	}

	private String genSTRMain(DocFile docFile, DocTopic topic) {
		String res = "" ;
		if(topic.getTopic().equals("section")) {
			res += 
			 "<tr class=SMain>"
		   + "<td colspan=\"2\" class=SEntry><a href=\"#" 
					 + topic.getQualifiedName()
					 + "\">" + topic.getTitle() + "</a>"
					 + "</td>"
		   + "</tr>" ;
		} else {
			res +=
			  "<tr class=\"SMain\">"
				   + "<td class=SIcon>"
							 + "<img src=" + getRelPathToHTML(topic.getDocFile().getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
							 + "</td>"
			+ "<td class=SEntry><a href=\"#" +topic.getTitle()+ "\" >" +topic.getTitle()+ "</a></td>" 
			+ "<td class=SDescription>" ;
		
			res += fMarkupToHTML.convertNDMarkupToHTML(docFile, topic, topic.getSummary(),HTMLFromNDMarkup.NDMarkupToHTMLStyle.General);
			res += "</tr>" ;
		}
		return res ;
	}	
	
	private String genTopicStart(DocTopic contentItem) {
		String res = 
				"<div class=\""
				  + HTMLUtils.genCSSClassForTopic(contentItem.getTopic()) 
				+"\">" ;
		return res ;
	}
	private String genClassEnd() {
		String res = 
				"</div>" ;
		return res ;
	}
	
	private String genContent(DocFile docFile) {
		String res = "" ;
		if(docFile.getChildren().size() > 1) {
			res += genFileSummary(docFile) ;
		}
		for(DocTopic contentItem: docFile.getChildren()) {
			if(!contentItem.getTopic().equals("section")) {
				res += genContent(docFile, contentItem) ;
			}
		}
		return res ;
	}
	
	private String genContent(DocFile docFile, DocTopic contentItem) {

		String res = "" ;
		res += genTopicStart(contentItem) ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(contentItem.getTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += genSummaryStart(docFile, contentItem) ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		res += genSTRMain(docFile,contentItem) ;
		res += genSummaryMembers(docFile, contentItem) ;
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		res += genClassEnd() ;
		res += genMemberDetail(docFile, contentItem) ;		
		return res ;		
	}

	private String genFileSummary(DocFile docFile) {
		String res = "" ;
		res += genSummaryStart(docFile, docFile) ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(docFile.getPageTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		for(DocTopic docItem: docFile.getChildren()) {
			res += genSTRMain(docFile,docItem) ;
			res += genSummaryMembers(docFile, docItem) ;
		}
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		return res ;
	}

	private String genSummaryMembers(DocFile docFile, DocTopic docTopic) {
		String res = "" ;
		boolean marked = false ;
		for(DocTopic child: docTopic.getChildren()) {
			res += genSummaryForMemember(docFile, docTopic, child, marked) ;
			marked = !marked ;
		}
		return res ;
	}
	
	private String genSummaryForMemember(DocFile docFile, DocTopic parent, DocTopic topic, boolean marked) {
		String res = "" ;
		if(topic.getTopic().equals("group")) {
			res += 
			 "<tr class=\"" + HTMLUtils.genCSSClassForTopicInSummary(topic.getTopic()) ;
			if(marked) {
				res += " SMarked" ;
			}
			res += " SIndent2\">" 
		   + "<td class=SIcon>"
					 + "</td>"
		   + "<td colspan=2 class=SEntry><a href=\"#" 
					 + topic.getQualifiedName()
					 + "\">" + topic.getTitle() + "</a>"
					 + "</td>"
		   + "</tr>" ;
		} else {
			res += 
			 "<tr class=\"" + HTMLUtils.genCSSClassForTopicInSummary(topic.getTopic()) ;
			if(marked) {
				res += " SMarked" ;
			}
			res += " SIndent3\">" 
		   + "<td class=SIcon>"
					 + "<img src=" + getRelPathToHTML(docFile.getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
					 + "</td>"
		   + "<td class=SEntry>"
		   			+"<a href=\"#" 
		   				+ topic.getQualifiedName()
		   				+ "\">" + topic.getTitle() + "</a>"
				 + "</td>"
		   + "<td class=SDescription>"
					 + topic.getSummary()
					 + "</td>"
		   + "</tr>" ;
		}
		return res ;
	}

	private String genDetails(DocFile docFile, DocTopic parent, DocTopic child) {
		String res =
				  "<div class=" + HTMLUtils.genCSSClassForTopic(child.getTopic()) + ">" 
				    + "<div class=CTopic>" 
					    + "<h3 class=CTitle>"
							+ "<a name=\"" 
								+ child.getQualifiedName()
						    + "\"></a>"
					    + child.getTitle()
					    + "</h3>"
					    + "<div class=CBody>" ; 
		res += fMarkupToHTML.convertNDMarkupToHTML(docFile, child, child.getBody(), HTMLFromNDMarkup.NDMarkupToHTMLStyle.General) ;
		res += 
					      "</div>"
				    + "</div>"
			    + "</div>" ;
		return res ;
	}
	
}



