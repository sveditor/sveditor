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

import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.model.DocClassItem;
import net.sf.sveditor.core.docs.model.DocModelNew;
import net.sf.sveditor.core.docs.model.DocPkgItem;

public class HTMLClassIndexFactory {
	
	private DocGenConfig cfg ;
	
	public HTMLClassIndexFactory(DocGenConfig cfg) {
		this.cfg = cfg ;
	}
	
	public String build(DocModelNew model) {
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart("..","Class Index") ;
		res += HTMLUtils.genBodyBegin("IndexPage") ;
		res += genIndex("..",model) ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu("..","Class Index") ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genIndex(String relPathToHTML, DocModelNew model) {
		String res = 
			"<div id=Index>"
				+ "<div class=IPageTitle>Class Index</div>"
				+ "<div class=INavigationBar>" ;
		boolean first = true ;
		Map<String, Map<String, Tuple<DocPkgItem,DocClassItem>>> classIdxMap = model.getClassIndexMap() ; 
		for(String idxKey: classIdxMap.keySet()) {
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
		for(String idxKey: classIdxMap.keySet()) {
		   if(classIdxMap.get(idxKey).size() == 0) { continue ; }
		   res +=
					  "<tr>"
						+"<td class=IHeading id=IFirstHeading>"
							+ "<a name=\"" + idxKey + "\"></a>" + idxKey + "</td><td></td>"
					+ "</tr>" ;
		   Map<String, Tuple<DocPkgItem, DocClassItem>> classMap = classIdxMap.get(idxKey) ;					
		   for(String className: classMap.keySet()) {
			   Tuple<DocPkgItem,DocClassItem> tuple = classMap.get(className) ;
			   String pkgName = tuple.first() == null ? "" : tuple.first().getName() ; 
			   String classRelPath = HTMLUtils.getHTMLRelPathForClass(cfg, pkgName, className).toString() ;
			   res +=
					  "<tr><td class=ISymbolPrefix id=IOnlySymbolPrefix>&nbsp;</td>" 
						+ "<td class=IEntry>"
							+ "<a href=\"" + relPathToHTML + "/" + classRelPath + "#" + className + "\" " 
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
	


}



