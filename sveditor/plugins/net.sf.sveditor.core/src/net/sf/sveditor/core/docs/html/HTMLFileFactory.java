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

package net.sf.sveditor.core.docs.html;

import java.io.File;

import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.model.DocFile;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.docs.model.DocTopic;

public class HTMLFileFactory {
	
	private DocGenConfig cfg ;
	private DocModel model ;
	
	public HTMLFileFactory(DocGenConfig cfg, DocModel model) {
		this.cfg = cfg ;
		this.model = model ;
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
	
	private String genSummaryStart(DocTopic docItem) {
		String result = "" ;
		result += docItem.getSummary() ;
		return result ;
	}

	private String genMemberDetail(DocTopic docTopic) {
		String res = "" ;
		for(DocTopic child: docTopic.getChildren()) {
			res += genDetails(docTopic, child) ;
		}
		return res ;
	}

	static String genSTRMain(DocTopic docItem) {
		String result =
			  "<tr class=\"SMain\">"
				   + "<td class=SIcon>"
							 + "<img src=" + getRelPathToHTML(docItem.getDocFile().getTitle()) + HTMLIconUtils.getImagePath(docItem) + ">"
							 + "</td>"
			+ "<td class=SEntry><a href=\"#" +docItem.getTitle()+ "\" >" +docItem.getTitle()+ "</a></td>" 
			+ "<td class=SDescription>" ;
		
			result += docItem.getSummary() ;
			result += "</tr>" ;
		return result ;
	}	
	
	private String genClassStart() {
		String res = 
				"<div class=\"CClass\">" ;
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
			res += genContent(docFile, contentItem) ;
		}
		return res ;
	}
	
	private String genContent(DocFile docFile, DocTopic contentItem) {

		String res = "" ;
		res += genClassStart() ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(contentItem.getTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += genSummaryStart(contentItem) ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		res += genSTRMain(contentItem) ;
		res += genSummaryMembers(docFile, contentItem) ;
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		res += genClassEnd() ;
		res += genMemberDetail(contentItem) ;		
		return res ;		
	}

	private String genFileSummary(DocFile docFile) {
		String res = "" ;
		res += genSummaryStart(docFile) ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(docFile.getPageTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		for(DocTopic docItem: docFile.getChildren()) {
			res += genSTRMain(docItem) ;
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
		for(DocTopic child: docTopic.getChildren()) {
			res += genSummaryForMemember(docFile, docTopic, child) ;
		}
		return res ;
	}
	
	private String genSummaryForMemember(DocFile docFile, DocTopic parent, DocTopic topic) {
		String res = 
			 "<tr class=\"" + HTMLUtils.genCSSClassForTopicName(topic.getTopic())
			 	+ " SIndent2\">" 
		   + "<td class=SIcon>"
					 + "<img src=" + getRelPathToHTML(docFile.getTitle()) + HTMLIconUtils.getImagePath(topic) + ">"
					 + "</td>"
		   + "<td class=SEntry><a href=\"#" 
					 + parent.getTitle()
					 + "." + topic.getTitle() 
					 + "\">" + topic.getTitle() + "</a>"
					 + "</td>"
		   + "<td class=SDescription>"
					 + topic.getSummary()
					 + "</td>"
		   + "</tr>" ;
		return res ;
	}

	private String genDetails(DocTopic parent, DocTopic child) {
		String res =
				  "<div class=" + HTMLUtils.genCSSClassForTopicName(child.getTopic()) + ">" 
				    + "<div class=CTopic>" 
					    + "<h3 class=CTitle>"
							+ "<a name=\"" 
							      + parent.getTitle() + "." + child.getTitle()
						    + "\"></a>"
					    + child.getTitle()
					    + "</h3>"
					    + "<div class=CBody>" ; 
		res += child.getBody() ;
		res += 
					      "</div>"
				    + "</div>"
			    + "</div>" ;
		return res ;
	}
	

	
}



