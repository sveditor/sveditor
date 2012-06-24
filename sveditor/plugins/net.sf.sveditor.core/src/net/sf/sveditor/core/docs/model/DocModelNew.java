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

import net.sf.sveditor.core.Tuple;

public class DocModelNew {
	
	public static final String IndexKeyWierd = "$#!" ;
	public static final String IndexKeyNum   = "0..9" ;
	
	private Map<String, DocPkgItem> pkgMap ;
	
	private Map<String, Map<String, DocClassItem>> classMapByPkg ;
	
	private Map<String, Map<String, Tuple<DocPkgItem,DocClassItem>>> classIndexMap ;
	
	public DocModelNew() {
		pkgMap = new HashMap<String, DocPkgItem>() ;
		classMapByPkg = new HashMap<String, Map<String, DocClassItem>>() ;
		classIndexMap = new HashMap<String, Map<String, Tuple<DocPkgItem,DocClassItem>>>() ;
		
		String keys[] = {IndexKeyWierd, IndexKeyNum,
						 "A","B","C","D","E","F","G",
						 "H","I","J","K","L","M","N",
						 "O","P","Q","R","S","T","U",
						 "V","W","X","Y","Z"} ;

	    for(String key: keys) {
	    	classIndexMap.put(key, new HashMap<String, Tuple<DocPkgItem,DocClassItem>>()) ;
	    }
	}

	public Map<String, DocPkgItem> getPkgMap() {
		return pkgMap ;
	}

	public Map<String, Map<String, DocClassItem>> getClassMapByPkg() {
		return classMapByPkg ;
	}

	public Map<String, Map<String, Tuple<DocPkgItem,DocClassItem>>> getClassIndexMap() {
		return classIndexMap ;
	}

}
