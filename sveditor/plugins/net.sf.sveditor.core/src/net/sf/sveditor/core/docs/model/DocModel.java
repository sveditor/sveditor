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
	
	private Map<String, DocFile> docFiles ;
	
	private Map<String, Map<String, DocTopic>> classMapByPkg ;
	
	private SymbolTable fSymbolTable ;
	
	public Map<String, Map<String, DocTopic>> getClassMapByPkg() {
		return classMapByPkg;
	}

	public void addDocFile(DocFile docFile) {
		docFiles.put(docFile.getTitle(),docFile) ;
	}
	
	public DocFile getDocFile(String filePath) {
		return docFiles.get(filePath) ;
	}
	
	public Set<String> getFileSet() {
		return docFiles.keySet() ;
	}
	
	public Collection<DocFile> getDocFiles() {
		return new HashSet<DocFile>(docFiles.values()) ;
	}

	public void setDocFiles(Map<String, DocFile> docFiles) {
		this.docFiles = docFiles;
	}

	private Map<String, DocIndex> indexMap ;
	
	private IDocTopicManager docTopicManager ;
	
	
	public DocModel() {
		docFiles = new HashMap<String, DocFile>() ;
		docTopicManager = new DocTopicManager() ;
		indexMap = new HashMap<String, DocIndex>() ;
		classMapByPkg = new HashMap<String, Map<String, DocTopic>> () ;
		fSymbolTable = new SymbolTable() ;
	}
	
	public SymbolTable getSymbolTable() {
		return fSymbolTable ;
	}

	public DocIndex getTopicIndexMap(String topic) {
		if(indexMap.containsKey(topic)) {
			return indexMap.get(topic) ;
		} else {
			return null ;
		}
	}
	
	public  DocIndex getCreateTopicIndexMap(String topic) {
		DocIndex index ;
		index = getTopicIndexMap(topic) ;
		if(index == null) {
			index = new DocIndex(topic) ;
			indexMap.put(topic, index) ;
		}
		return index ;
	}

	public IDocTopicManager getDocTopics() {
		return docTopicManager ;
	}
		

}
