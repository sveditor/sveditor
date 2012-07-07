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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.IDocTopicManager;

public class DocModel {
	
	public static final String IndexKeyWierd = "$#!" ;
	public static final String IndexKeyNum   = "0..9" ;
	
	public static final String indexKeys[] = 
		{IndexKeyWierd, IndexKeyNum,
		"A","B","C","D","E","F","G",
		"H","I","J","K","L","M","N",
		"O","P","Q","R","S","T","U",
		"V","W","X","Y","Z"} ;
	
	private Map<String, DocFile> docFiles ;
	
	public void addDocFile(DocFile docFile) {
		docFiles.put(docFile.getTitle(),docFile) ;
	}
	
	public DocFile getDocFile(String filePath) {
		return docFiles.get(filePath) ;
	}
	
	public Set<String> getFileSet() {
		return docFiles.keySet() ;
	}
	
	public Collection<DocTopic> getDocItems() {
		return new HashSet<DocTopic>(docFiles.values()) ;
	}

	public void setDocFiles(Map<String, DocFile> docFiles) {
		this.docFiles = docFiles;
	}

	private Map<String, DocPkgItem> pkgMap ;
	
	private Map<String, Map<String, DocClassItem>> classMapByPkg ;
	
	private Map<String, Map<String, Map<String, DocTopic>>> topicIndexMaps ;
	
	private IDocTopicManager docTopicManager ;
	
	public DocModel() {
		pkgMap = new HashMap<String, DocPkgItem>() ;
		classMapByPkg = new HashMap<String, Map<String, DocClassItem>>() ;
		docFiles = new HashMap<String, DocFile>() ;
		docTopicManager = new DocTopicManager() ;
		topicIndexMaps = new HashMap<String, Map<String, Map<String,DocTopic>>>() ;
	}

	public Map<String, DocPkgItem> getPkgMap() {
		return pkgMap ;
	}

	public Map<String, Map<String, DocClassItem>> getClassMapByPkg() {
		return classMapByPkg ;
	}

	public Map<String,Map<String,DocTopic>> getTopicIndexMap(String topic) {
		if(topicIndexMaps.containsKey(topic)) {
			return topicIndexMaps.get(topic) ;
		} else {
			return null ;
		}
	}
	
	public Map<String,Map<String,DocTopic>> getCreateTopicIndexMap(String topic) {
		Map<String,Map<String,DocTopic>> res ;
		res = getTopicIndexMap(topic) ;
		if(res == null) {
			res = new HashMap<String,Map<String,DocTopic>>() ;
			for(String key: indexKeys) {
				res.put(key, new HashMap<String, DocTopic>()) ;
			}
			topicIndexMaps.put(topic, res) ;
		}
		return res ;
	}

	public IDocTopicManager getDocTopics() {
		return docTopicManager ;
	}
		

}
