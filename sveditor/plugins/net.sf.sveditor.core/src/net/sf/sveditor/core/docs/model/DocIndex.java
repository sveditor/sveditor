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

package net.sf.sveditor.core.docs.model;

import java.util.HashMap;
import java.util.Map;

public class DocIndex {
	
	public static final String IndexKeyWierd = "$#!" ;
	public static final String IndexKeyNum   = "0..9" ;
	
	public static final String indexKeys[] = 
		{IndexKeyWierd, IndexKeyNum,
		"A","B","C","D","E","F","G",
		"H","I","J","K","L","M","N",
		"O","P","Q","R","S","T","U",
		"V","W","X","Y","Z"} ;
	
	private Map<String, Map<String,DocTopic>> fMap ;
	
	private String fTopicName ;
	
	public DocIndex(String topicName) {
		setTopicName(topicName) ;
		fMap = new HashMap<String,Map<String,DocTopic>>() ;
		for(String key: indexKeys) {
			fMap.put(key, new HashMap<String, DocTopic>()) ;
		}
	}

	public String getTopicName() {
		return fTopicName;
	}

	public void setTopicName(String topicName) {
		this.fTopicName = topicName;
	}
	
	public Map<String, Map<String,DocTopic>> getMap() {
		return fMap ;
	}
	
	public void indexTopic(DocTopic docTopic) {
		String name = docTopic.getTitle() ;
		String firstChar = name.substring(0, 1).toUpperCase() ;
		if(fMap.containsKey(firstChar)) {
			fMap.get(firstChar)
				.put(name, docTopic) ;
		} else if(firstChar.matches("[0123456789]")) {
			fMap.get(IndexKeyNum)
				.put(name,docTopic) ;
		} else {
			fMap.get(IndexKeyWierd)
				.put(name,docTopic) ;
		}		
	}
	
}
