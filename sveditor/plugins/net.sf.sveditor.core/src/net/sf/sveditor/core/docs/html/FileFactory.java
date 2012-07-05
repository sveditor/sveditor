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
import net.sf.sveditor.core.docs.model.DocClassItem;
import net.sf.sveditor.core.docs.model.DocFile;
import net.sf.sveditor.core.docs.model.DocFuncItem;
import net.sf.sveditor.core.docs.model.DocItem;
import net.sf.sveditor.core.docs.model.DocItemType;
import net.sf.sveditor.core.docs.model.DocTaskItem;
import net.sf.sveditor.core.docs.model.DocVarDeclItem;

public class FileFactory {
	
	@SuppressWarnings("unused")
	private DocGenConfig cfg ;
	
	public FileFactory(DocGenConfig cfg) {
		this.cfg = cfg ;
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
		res += HTMLUtils.genHTMLHeadStart(getRelPathToHTML(docFile.getName()),"FIXME-I-NEED-A-TITLE") ;
		res += HTMLUtils.genBodyBegin("ContentPage") ;
		res += HTMLUtils.genContentBegin() ;
		res += genContent(docFile) ;
		res += HTMLUtils.genContentEnd() ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu(getRelPathToHTML(docFile.getName()),"FIXME-I-NEED-A-SOMETHING") ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	
	private String genSummaryStart(DocClassItem classItem) {
		String result = "" ;
		result += classItem.getSummary() ;
		return result ;
	}

	private String genMemberDetail(DocClassItem classItem) {
		String res = "" ;
		for(DocItem child: classItem.getChildren()) {
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
							 + "<img src=" + getRelPathToHTML(classItem.getDocFile().getName()) + HTMLIconUtils.getImagePath(classItem) + ">"
							 + "</td>"
			+ "<td class=SEntry><a href=\"#" +classItem.getName()+ "\" >" +classItem.getName()+ "</a></td>" 
			+ "<td class=SDescription>" ;
		
			result += classItem.getSummary() ;
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
		for(DocItem contentItem: docFile.getChildren()) {
			switch(contentItem.getType()) {
			case CLASS: {
				res += genClass((DocClassItem)contentItem) ;
				break ;
			}
			default: { }
			}
		}
		return res ;
	}
	
	private String genClass(DocClassItem classItem) {
		String res = "" ;
		res += genClassStart() ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(classItem.getQualifiedName()) ;
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
		return res ;
	}

	private String genSummaryMembers(DocClassItem classItem) {
		String res = "" ;
		for(DocItem child: classItem.getChildren()) {
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
						 + classItem.getName()
						 + "." + varItem.getName() 
						 + "\">" + varItem.getName() + "</a>"
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
					 + classItem.getName()
					 + "." + task.getName() 
					 + "\">" + task.getName() + "()</a>"
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
					 + classItem.getName()
					 + "." + func.getName() 
					 + "\">" + func.getName() + "()</a>"
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
						  + classItem.getName() + "." + taskItem.getName()
				    + "\"></a>"
				    + taskItem.getName() + "()"
				    + "</h3>"
				    + "<div class=CBody>" ;
		res += taskItem.getBody() ;
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
						  + classDeclItem.getName() + "." + func.getName()
				    + "\"></a>"
				    + func.getName() + "()"
				    + "</h3>"
				    + "<div class=CBody>" ;
		res += func.getBody() ;
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
								  + classDeclItem.getName() + "." + varItem.getName()
						    + "\"></a>"
					    + varItem.getName()
					    + "</h3>"
					    + "<div class=CBody>" ; 
		res += varItem.getBody() ;
		res += 
					      "</div>"
				    + "</div>"
			    + "</div>" ;
		return res ;
	}

}



