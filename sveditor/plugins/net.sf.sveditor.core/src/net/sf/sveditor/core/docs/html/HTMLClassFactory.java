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


public class HTMLClassFactory {
	
	/*
	
	@SuppressWarnings("unused")
	private DocGenConfig cfg ;
	
	public HTMLClassFactory(DocGenConfig cfg) {
		this.cfg = cfg ;
	}
	
	public String build(DocClassItem classItem) {
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart("../..",classItem.getTitle()) ;
		res += HTMLUtils.genBodyBegin("ContentPage") ;
		res += HTMLUtils.genContentBegin() ;
		res += genClassStart() ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(classItem.getTitle()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += genSummaryStart(classItem) ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		res += genSTRMain(classItem) ;
		res += genSummaryMembers(classItem) ;
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		res += genClassEnd() ;
		res += genMemberDetail(classItem) ;
		res += HTMLUtils.genContentEnd() ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu("../..", classItem.getTitle()) ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genSummaryStart(DocClassItem classItem) {
		String result = "" ;
		// Note: this iteration of topics attached to the class item seems wrong.
		// Will there be more than one topic for class? If not, then
		// the contained set of topics (which is just one topic) can be 
		// swallowed by the class item.
		for(DocTopic topic: classItem.getChildren()) {
			result += topic.getBody() ;
		}
		return result ;
	}

	private String genMemberDetail(DocClassItem classItem) {
		String res = "" ;
		for(DocTopic child: classItem.getChildren()) {
			if(child.getType() == DocItemType.VARDECL) 
				res += genDetailsVar(classItem, (DocVarDeclItem)child) ;
			else if(child.getType() == DocItemType.FUNC) 
				res += genDetailsFunc(classItem, (DocFuncItem)child) ;
			else if(child.getType() == DocItemType.TASK) 
				res += genDetailsTask(classItem, (DocTaskItem)child) ;
		}
		return res ;
	}

	static String genSTRMain(DocClassItem classItem) {
		String result =
			  "<tr class=\"SMain\">"
				   + "<td class=SIcon>"
							 + "<img src=../../" + HTMLIconUtils.getImagePath(classItem) + ">"
							 + "</td>"
			+ "<td class=SEntry><a href=\"#" +classItem.getTitle()+ "\" >" +classItem.getTitle()+ "</a></td>" 
			+ "<td class=SDescription>" ;
		
			result += classItem.getSummary() ;

////		if(classItem.getTopics().size()==0) {
//			result += 
//				  "This will become the class description" + "</td>" ;
////		} else {
////			for(DocTopic topic: classItem.getTopics()) {
////				result += topic.getBody() ;
////			}
////		}
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
	
	private String genSummaryMembers(DocClassItem classItem) {
		String res = "" ;
		for(DocTopic child: classItem.getChildren()) {
			if(child.getType() == DocItemType.VARDECL) 
				res += genSummaryVarDecl(classItem, (DocVarDeclItem)child) ;
			else if(child.getType() == DocItemType.FUNC) 
				res += genSummaryFuncDecl(classItem, (DocFuncItem)child) ;
			else if(child.getType() == DocItemType.TASK) 
				res += genSummaryTaskDecl(classItem, (DocTaskItem)child) ;
		}
		return res ;
	}

	private String genSummaryVarDecl(DocClassItem classItem, DocVarDeclItem varItem) {
		String res =
				 "<tr class=\"SVariable SIndent2 SMarked\">" 
			   + "<td class=SIcon>"
						 + "<img src=../../" + HTMLIconUtils.getImagePath(varItem) + ">"
						 + "</td>"
			   + "<td class=SEntry><a href=\"#" 
						 + classItem.getTitle()
						 + "." + varItem.getTitle() 
						 + "\">" + varItem.getTitle() + "</a>"
						 + "</td>"
			   + "<td class=SDescription>"
						 + varItem.getSummary()
						 + "</td>"
			   + "</tr>" ;
		return res ;
	}
	
	private String genSummaryTaskDecl(DocClassItem classItem, DocTaskItem task) {
		String res = 
			 "<tr class=\"SFunction SIndent2\">" 
		   + "<td class=SIcon>"
					 + "<img src=../../" + HTMLIconUtils.getImagePath(task) + ">"
					 + "</td>"
		   + "<td class=SEntry><a href=\"#" 
					 + classItem.getTitle()
					 + "." + task.getTitle() 
					 + "\">" + task.getTitle() + "()</a>"
					 + "</td>"
		   + "<td class=SDescription>"
					 + task.getSummary()
					 + "</td>"
		   + "</tr>" ;
		return res ;
	}


	private String genSummaryFuncDecl(DocClassItem classItem, DocFuncItem func) {
		String res = 
			 "<tr class=\"SFunction SIndent2\">" 
		   + "<td class=SIcon>"
					 + "<img src=../../" + HTMLIconUtils.getImagePath(func) + ">"
					 + "</td>"
		   + "<td class=SEntry><a href=\"#" 
					 + classItem.getTitle()
					 + "." + func.getTitle() 
					 + "\">" + func.getTitle() + "()</a>"
					 + "</td>"
		   + "<td class=SDescription>"
					 + func.getSummary()
					 + "</td>"
		   + "</tr>" ;
		return res ;
	}
	
	private String genDetailsTask(DocClassItem classItem, DocTaskItem taskItem) {
		String res = 
			  "<div class=CFunction>"
			    + "<div class=CTopic><h3 class=CTitle><a name=\"" 
						  + classItem.getTitle() + "." + taskItem.getTitle()
				    + "\"></a>"
				    + taskItem.getTitle() + "()"
				    + "</h3>"
				    + "<div class=CBody>" ;
		for(DocTopic topic: taskItem.getChildren()) {
			res += topic.getBody() ;
		}
		res +=
				      "</div>"
			    + "</div>"
		    + "</div>" ;
		return res ;
	}

	private String genDetailsFunc(DocClassItem classDeclItem, DocFuncItem func) {
		String res = 
			  "<div class=CFunction>"
			    + "<div class=CTopic><h3 class=CTitle><a name=\"" 
						  + classDeclItem.getTitle() + "." + func.getTitle()
				    + "\"></a>"
				    + func.getTitle() + "()"
				    + "</h3>"
				    + "<div class=CBody>" ;
		for(DocTopic topic: func.getChildren()) {
			res += topic.getBody() ;
		}
		res +=
				      "</div>"
			    + "</div>"
		    + "</div>" ;
		return res ;
	}

	private String genDetailsVar(DocClassItem classDeclItem, DocVarDeclItem varItem) {
		String res =
				  "<div class=\"CVariable\">"
				    + "<div class=CTopic>" 
					    + "<h3 class=CTitle>"
							+ "<a name=\"" 
								  + classDeclItem.getTitle() + "." + varItem.getTitle()
						    + "\"></a>"
					    + varItem.getTitle()
					    + "</h3>"
					    + "<div class=CBody>" ; 
		for(DocTopic topic: varItem.getChildren()) {
			res += topic.getBody() ;
		}
		res += 
					      "</div>"
				    + "</div>"
			    + "</div>" ;
		return res ;
	}
	
	*/

}



