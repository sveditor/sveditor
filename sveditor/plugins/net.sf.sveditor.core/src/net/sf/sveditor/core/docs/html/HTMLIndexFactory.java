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
import java.util.Collections;
import java.util.Map;

import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.DocTopicType;
import net.sf.sveditor.core.docs.model.DocItem;
import net.sf.sveditor.core.docs.model.DocModel;

public class HTMLIndexFactory {
	
	private DocGenConfig cfg ;
	private DocTopicType docTopicType ;
	
	public HTMLIndexFactory(DocGenConfig cfg, DocTopicType docTopicType) {
		this.cfg = cfg ;
		this.docTopicType = docTopicType ;
	}
	
	public String build(DocModel model) {
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart("..","Class Index") ;
		res += HTMLUtils.genBodyBegin("IndexPage") ;
		res += genIndex("..",model) ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu("..","Class Index") ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genIndex(String relPathToHTML, DocModel model) {
		Map<String, Map<String, DocItem>> classIdxMap = model.getTopicIndexMap("class") ;
		if(classIdxMap == null) {
			return "" ;
		}
		String res = 
			"<div id=Index>"
				+ "<div class=IPageTitle>Class Index</div>"
				+ "<div class=INavigationBar>" ;
		boolean first = true ;
		ArrayList<String> sortedIdxKeys = new ArrayList<String>(classIdxMap.keySet()) ;
		Collections.sort(sortedIdxKeys) ;
		for(String idxKey: sortedIdxKeys) {
			if(!first) { res += " &middot; " ; } 
			else { first = false ; }
			if(classIdxMap.get(idxKey).size() == 0) {
				res += idxKey ;
			} else {
				res += "<a href=\"#" + idxKey.toUpperCase() 
						+ "\">" + idxKey.toUpperCase() 
						+ "</a>";
			}
			
		}
		res += 
				"</div>"
				+ "<table border=0 cellspacing=0 cellpadding=0>" ;
		for(String idxKey: sortedIdxKeys) {
		   if(classIdxMap.get(idxKey).size() == 0) { continue ; }
		   res +=
					  "<tr>"
						+"<td class=IHeading id=IFirstHeading>"
							+ "<a name=\"" + idxKey + "\"></a>" + idxKey + "</td><td></td>"
					+ "</tr>" ;
		   Map<String, DocItem> classMap = classIdxMap.get(idxKey) ;
		   ArrayList<String> sortedClassNames = new ArrayList<String>(classMap.keySet()) ;
		   Collections.sort(sortedClassNames) ;
		   for(String className: sortedClassNames) {
			   DocItem docItem = classMap.get(className) ;
			   res +=
					  "<tr><td class=ISymbolPrefix id=IOnlySymbolPrefix>&nbsp;</td>" 
						+ "<td class=IEntry>"
							+ "<a href=\"" + relPathToHTML + "/files" + docItem.getDocFile().getDocPath() + ".html" + "#" + docItem.getQualifiedName() + "\" " 
//								+ "id=link1 onMouseOver=\"ShowTip(event, 'tt1', 'link1')\" "
//								+ "onMouseOut=\"HideTip('tt1')\" "
								+ "class=ISymbol>" + className + "</a>"
						+ "</td>"
					+ "</tr>" ;
		   }
		}
		res += 
				  "</table>" 
//				+ "<div class=CToolTip id=\"tt1\">"
//					+ "<div class=CClass>The uvm_object class is the base class for all UVM data and hierarchical classes. </div>"
//				+"</div>" 
			+ "</div><!--Index-->" ;	
		return res ;
	}
	
//	private String genIndex(String relPathToHTML, DocModel model) {
//		String res = 
//			"<div id=Index>"
//				+ "<div class=IPageTitle>Class Index</div>"
//				+ "<div class=INavigationBar>" ;
//		boolean first = true ;
//		Map<String, Map<String, Tuple<DocPkgItem,DocClassItem>>> classIdxMap = model.getClassIndexMap("class") ; 
//		ArrayList<String> sortedIdxKeys = new ArrayList<String>(classIdxMap.keySet()) ;
//		Collections.sort(sortedIdxKeys) ;
//		for(String idxKey: sortedIdxKeys) {
//			if(!first) { res += " &middot; " ; } 
//			else { first = false ; }
//			if(classIdxMap.get(idxKey).size() == 0) {
//				res += idxKey ;
//			} else {
//				res += "<a href=\"#" + idxKey.toUpperCase() 
//						+ "\">" + idxKey.toUpperCase() 
//						+ "</a>";
//			}
//			
//		}
//		res += 
//				"</div>"
//				+ "<table border=0 cellspacing=0 cellpadding=0>" ;
//		for(String idxKey: sortedIdxKeys) {
//		   if(classIdxMap.get(idxKey).size() == 0) { continue ; }
//		   res +=
//					  "<tr>"
//						+"<td class=IHeading id=IFirstHeading>"
//							+ "<a name=\"" + idxKey + "\"></a>" + idxKey + "</td><td></td>"
//					+ "</tr>" ;
//		   Map<String, Tuple<DocPkgItem, DocClassItem>> classMap = classIdxMap.get(idxKey) ;					
//		   ArrayList<String> sortedClassNames = new ArrayList<String>(classMap.keySet()) ;
//		   Collections.sort(sortedClassNames) ;
//		   for(String className: sortedClassNames) {
//			   Tuple<DocPkgItem,DocClassItem> tuple = classMap.get(className) ;
//			   String pkgName = tuple.first() == null ? "" : tuple.first().getName() ; 
//			   String classRelPath = HTMLUtils.getHTMLRelPathForClass(cfg, pkgName, className).toString() ;
//			   res +=
//					  "<tr><td class=ISymbolPrefix id=IOnlySymbolPrefix>&nbsp;</td>" 
//						+ "<td class=IEntry>"
//							+ "<a href=\"" + relPathToHTML + "/" + classRelPath + "#" + className + "\" " 
////								+ "id=link1 onMouseOver=\"ShowTip(event, 'tt1', 'link1')\" "
////								+ "onMouseOut=\"HideTip('tt1')\" "
//								+ "class=ISymbol>" + className + "</a>"
//						+ "</td>"
//					+ "</tr>" ;
//		   }
//		}
//		res += 
//				  "</table>" 
////				+ "<div class=CToolTip id=\"tt1\">"
////					+ "<div class=CClass>The uvm_object class is the base class for all UVM data and hierarchical classes. </div>"
////				+"</div>" 
//			+ "</div><!--Index-->" ;	
//		return res ;
//	}
//	


}



