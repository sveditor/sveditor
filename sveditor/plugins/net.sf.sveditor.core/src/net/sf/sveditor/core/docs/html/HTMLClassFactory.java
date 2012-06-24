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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.docs.DocGenConfig;

public class HTMLClassFactory {
	
	@SuppressWarnings("unused")
	private DocGenConfig cfg ;
	
	public HTMLClassFactory(DocGenConfig cfg) {
		this.cfg = cfg ;
	}
	
	public String build(SVDBDeclCacheItem classDeclItem) {
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart("../..",classDeclItem.getName()) ;
		res += HTMLUtils.genBodyBegin("ContentPage") ;
		res += HTMLUtils.genContentBegin() ;
		res += genClassStart() ;
		res += HTMLUtils.genCTopicBegin("MainTopic") ;
		res += HTMLUtils.genCTitle(classDeclItem.getName()) ;
		res += HTMLUtils.genCBodyBegin() ;
		res += HTMLUtils.genSummaryBegin() ;
		res += HTMLUtils.genSTitle() ;
		res += HTMLUtils.genSBorderBegin() ;
		res += HTMLUtils.genSTableBegin() ;
		res += genSTRMain(classDeclItem) ;
		res += genSummaryMembers(classDeclItem) ;
		res += HTMLUtils.genSTableEnd() ;
		res += HTMLUtils.genSBorderEnd() ;
		res += HTMLUtils.genSummaryEnd() ;
		res += HTMLUtils.genCBodyEnd() ;
		res += HTMLUtils.genCTopicEnd() ;
		res += genClassEnd() ;
		res += genMemberDetail(classDeclItem) ;
		res += HTMLUtils.genContentEnd() ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu("../..") ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genMemberDetail(SVDBDeclCacheItem classDeclItem) {
		String res = "" ;
		List<ISVDBItemBase> members = new ArrayList<ISVDBItemBase>();
		ISVDBItemBase it = classDeclItem.getSVDBItem() ;
		if (it instanceof ISVDBChildParent) {
			for (ISVDBChildItem ci : ((ISVDBChildParent)it).getChildren()) {
				members.add(ci);
			}
		}
		for(ISVDBItemBase child: members) {
			if(child.getType() == SVDBItemType.VarDeclStmt) 
				res += genDetailsVar(classDeclItem, child) ;
			else if(child.getType() == SVDBItemType.Function) 
				res += genDetailsFunc(classDeclItem, child) ;
			else if(child.getType() == SVDBItemType.Task) 
				res += genDetailsTask(classDeclItem, child) ;
		}
		return res ;
	}

	static String genSTRMain(SVDBDeclCacheItem classDeclItem) {
		String result =
			  "<tr class=\"SMain\">"
				   + "<td class=SIcon>"
							 + "<img src=../../" + HTMLIconUtils.getImagePath(classDeclItem.getSVDBItem()) + ">"
							 + "</td>"
			+ "<td class=SEntry><a href=\"#" +classDeclItem.getName()+ "\" >" +classDeclItem.getName()+ "</a></td>" 
			+ "<td class=SDescription>" + "This will become the class description" + "</td>"
			+ "</tr>" ;
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
	
	private String genSummaryMembers(SVDBDeclCacheItem classDeclItem) {
		String res = "" ;
		List<ISVDBItemBase> members = new ArrayList<ISVDBItemBase>();
		ISVDBItemBase it = classDeclItem.getSVDBItem() ;
		if (it instanceof ISVDBChildParent) {
			for (ISVDBChildItem ci : ((ISVDBChildParent)it).getChildren()) {
				members.add(ci);
			}
		}
		for(ISVDBItemBase child: members) {
			if(child.getType() == SVDBItemType.VarDeclStmt) 
				res += genSummaryVarDecl(classDeclItem, child) ;
			else if(child.getType() == SVDBItemType.Function) 
				res += genSummaryFuncDecl(classDeclItem, child) ;
			else if(child.getType() == SVDBItemType.Task) 
				res += genSummaryTaskDecl(classDeclItem, child) ;
		}
		return res ;
	}

	private String genSummaryVarDecl(SVDBDeclCacheItem classDeclItem, ISVDBItemBase item) {
		if(!(item instanceof SVDBVarDeclStmt)) { return "" ; }
		String res = "" ;
		SVDBVarDeclStmt varDecl = (SVDBVarDeclStmt)item ;
		for(ISVDBChildItem child: varDecl.getChildren()) {
			if(!(child instanceof SVDBVarDeclItem)) { continue ; }
			SVDBVarDeclItem varDeclItem = (SVDBVarDeclItem)child ;
			res += 
				 "<tr class=\"SVariable SIndent2 SMarked\">" 
			   + "<td class=SIcon>"
						 + "<img src=../../" + HTMLIconUtils.getImagePath(child) + ">"
						 + "</td>"
			   + "<td class=SEntry><a href=\"#" 
						 + classDeclItem.getName()
						 + "." + varDeclItem.getName() 
						 + "\">" + varDeclItem.getName() + "</a>"
						 + "</td>"
			   + "<td class=SDescription>"
						 + "This will be the variable description"
						 + "</td>"
			   + "</tr>" ;
		}
		return res ;
	}
	
	private String genSummaryTaskDecl(SVDBDeclCacheItem classDeclItem, ISVDBItemBase child) {
		if(!(child instanceof SVDBTask)) { return "" ; } 
		SVDBTask task = (SVDBTask)child ;
		String res = 
			 "<tr class=\"SFunction SIndent2\">" 
		   + "<td class=SIcon>"
					 + "<img src=../../" + HTMLIconUtils.getImagePath(child) + ">"
					 + "</td>"
		   + "<td class=SEntry><a href=\"#" 
					 + classDeclItem.getName()
					 + "." + task.getName() 
					 + "\">" + task.getName() + "()</a>"
					 + "</td>"
		   + "<td class=SDescription>"
					 + "This will be the variable description"
					 + "</td>"
		   + "</tr>" ;
		return res ;
	}


	private String genSummaryFuncDecl(SVDBDeclCacheItem classDeclItem, ISVDBItemBase child) {
		if(!(child instanceof SVDBFunction)) { return "" ; } 
		SVDBFunction func = (SVDBFunction)child ;
		String res = 
			 "<tr class=\"SFunction SIndent2\">" 
		   + "<td class=SIcon>"
					 + "<img src=../../" + HTMLIconUtils.getImagePath(child) + ">"
					 + "</td>"
		   + "<td class=SEntry><a href=\"#" 
					 + classDeclItem.getName()
					 + "." + func.getName() 
					 + "\">" + func.getName() + "()</a>"
					 + "</td>"
		   + "<td class=SDescription>"
					 + "This will be the variable description"
					 + "</td>"
		   + "</tr>" ;
		return res ;
	}
	
	private String genDetailsTask(SVDBDeclCacheItem classDeclItem, ISVDBItemBase child) {
		if(!(child instanceof SVDBTask)) { return "" ; } 
		SVDBTask task = (SVDBTask)child ;
		String res = 
			  "<div class=CFunction>"
			    + "<div class=CTopic><h3 class=CTitle><a name=\"" 
						  + classDeclItem.getName() + "." + task.getName()
				    + "\"></a>"
				    + task.getName() + "()"
				    + "</h3>"
				    + "<div class=CBody>"
						+ "<p>This is some text about the variable</p>"
				    + "</div>"
			    + "</div>"
		    + "</div>" ;
		return res ;
	}

	private String genDetailsFunc(SVDBDeclCacheItem classDeclItem, ISVDBItemBase child) {
		if(!(child instanceof SVDBFunction)) { return "" ; } 
		SVDBFunction func = (SVDBFunction)child ;
		String res = 
			  "<div class=CFunction>"
			    + "<div class=CTopic><h3 class=CTitle><a name=\"" 
						  + classDeclItem.getName() + "." + func.getName()
				    + "\"></a>"
				    + func.getName() + "()"
				    + "</h3>"
				    + "<div class=CBody>"
						+ "<p>This is some text about the variable</p>"
				    + "</div>"
			    + "</div>"
		    + "</div>" ;
		return res ;
	}

	private String genDetailsVar(SVDBDeclCacheItem classDeclItem, ISVDBItemBase item) {
		if(!(item instanceof SVDBVarDeclStmt)) { return "" ; }
		String res = "" ;
		SVDBVarDeclStmt varDecl = (SVDBVarDeclStmt)item ;
		for(ISVDBChildItem child: varDecl.getChildren()) {
			if(!(child instanceof SVDBVarDeclItem)) { continue ; }
			SVDBVarDeclItem varDeclItem = (SVDBVarDeclItem)child ;
			res += 
				  "<div class=\"CVariable\">"
				    + "<div class=CTopic>" 
					    + "<h3 class=CTitle>"
							+ "<a name=\"" 
								  + classDeclItem.getName() + "." + varDeclItem.getName()
						    + "\"></a>"
					    + varDeclItem.getName()
					    + "</h3>"
					    + "<div class=CBody>"
							+ "<p>This is some text about the variable</p>"
					    + "</div>"
				    + "</div>"
			    + "</div>" ;
		}
		return res ;
	}

}



