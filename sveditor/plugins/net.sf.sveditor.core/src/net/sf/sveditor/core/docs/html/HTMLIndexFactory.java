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

package net.sf.sveditor.core.docs.html;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.DocTopicType;
import net.sf.sveditor.core.docs.model.DocIndex;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

@SuppressWarnings("unused")
public class HTMLIndexFactory {
	
	private DocGenConfig cfg ;
	private DocTopicType docTopicType ;
	private LogHandle fLog ;
	String fIndexNameCapitalized ;
	
	private int ttID = 0 ;
	private int linkID = 0 ;
	
	private HashMap<String,String> ttDescriptions ;
	
	public HTMLIndexFactory(DocGenConfig cfg, DocTopicType docTopicType) {
		this.cfg = cfg ;
		this.docTopicType = docTopicType ;
		fLog = LogFactory.getLogHandle("HTMLIndexFactory") ;
		fIndexNameCapitalized = docTopicType.getNameCapitalized() + " Index" ;
		ttDescriptions = new HashMap<String,String>() ;
	}
	
	public String build(DocModel model) {
		fLog.debug(ILogLevel.LEVEL_MIN,
				String.format("Building index for topic(%s)",
					docTopicType.getName())) ;
		String res = HTMLUtils.STR_DOCTYPE ;
		res += HTMLUtils.genHTMLHeadStart("..",fIndexNameCapitalized) ;
		res += HTMLUtils.genBodyBegin("IndexPage") ;
		res += genIndex("..",model) ;
		res += HTMLUtils.genFooter() ;
		res += HTMLUtils.genMenu(cfg,"..",fIndexNameCapitalized,model.getDocTopics().getAllTopicTypes()) ;
		res += HTMLUtils.genBodyHTMLEnd() ;
		return res ;
	}
	
	private String genIndex(String relPathToHTML, DocModel model) {
		DocIndex idxMap = model.getTopicIndexMap(docTopicType.getName().toLowerCase()) ;
		if(idxMap == null) {
			return "" ;
		}
		String res = 
			"<div id=Index>"
				+ "<div class=IPageTitle>" 
					+ fIndexNameCapitalized
					+ "</div>"
				+ "<div class=INavigationBar>" ;
		boolean first = true ;
		ArrayList<String> sortedIdxKeys = new ArrayList<String>(idxMap.getMap().keySet()) ;
		Collections.sort(sortedIdxKeys) ;
		for(String idxKey: sortedIdxKeys) {
			if(!first) { res += " &middot; " ; } 
			else { first = false ; }
			if(idxMap.getMap().get(idxKey).size() == 0) {
				res += idxKey ;
			} else {
				res += "<a href=\"#" + idxKey.toUpperCase() 
						+ "\">" + idxKey.toUpperCase() 
						+ "</a>";
			}
			
		}
		res += 
				"</div>"
				+ "<table class=ITable border=0 cellspacing=0 cellpadding=0>" ;
		for(String idxKey: sortedIdxKeys) {
		   if(idxMap.getMap().get(idxKey).size() == 0) { continue ; }
		   res +=
					  "<tr>"
						+"<td class=IHeading id=IFirstHeading>"
							+ "<a name=\"" + idxKey + "\"></a>" + idxKey + "</td><td></td>"
					+ "</tr>" ;
		   ArrayList<DocTopic> entries = new ArrayList<DocTopic>(idxMap.getMap().get(idxKey)) ;
		   Collections.sort(entries, new Comparator<DocTopic>() {
			public int compare(DocTopic o1, DocTopic o2) {
				return (o1.getTitle() + "::" + o1.getQualifiedName())
							.compareToIgnoreCase(
									(o2.getTitle() + "::" + o2.getQualifiedName())) ; }}) ;
		   for(DocTopic entry: entries) {
			   String linkID = getNextLinkID() ;
			   String ttID = getNextTTID() ;
			   res +=
					  "<tr><td class=ISymbolPrefix id=IOnlySymbolPrefix>&nbsp;</td>" 
						+ "<td class=IEntry>"
							+ "<a href=\"" + relPathToHTML + "/files" 
								+ entry.getDocFile().getDocPath() 
								+ ".html" + "#" + entry.getQualifiedName() + "\" " 
								+ "id=" + linkID + " onMouseOver=\"ShowTip(event, '" + ttID + "', '" + linkID + "')\" "
								+ "onMouseOut=\"HideTip('" + ttID + "')\" "
								+ "class=ISymbol>" + entry.getTitle() + "</a>"
						+ "</td>"
						+ "<td class=IDescription>"
							+ entry.getQualifiedName()
			   	        + "</td>"
					+ "</tr>" ;
			   ttDescriptions.put(ttID, entry.getSummary()) ;
		   }
		}
		res += 
				  "</table>"  ;
		res += genToolTips() ;
		res += "</div><!--Index-->" ;	
		return res ;
	}

	private String genToolTips() {
		String res = "" ;
		for(String ttid: ttDescriptions.keySet()) {
			res += 
				  "<div class=CToolTip id=\"" + ttid +"\">"
					+ "<div class=CClass>" + ttDescriptions.get(ttid) + "</div>"
				+"</div>"  ;
		}
		return res ;
	}

	private String getNextTTID() {
		ttID += 1 ;
		return "tt" + ttID ;
	}

	private String getNextLinkID() {
		linkID += 1 ;
		return "linkID" + linkID ;
	}


}



