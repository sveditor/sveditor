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

package net.sf.sveditor.core.docs ;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.docs.DocTopicType.ScopeType;

public class DocTopicManager implements IDocTopicManager {
	
	public static String TOPIC_GENERAL 		= "general";
//	public static String TOPIC_GENERIC 		= "generic";
	public static String TOPIC_GROUP 		= "group";
	public static String TOPIC_MODULE 		= "module";
	public static String TOPIC_CLASS 		= "class";
	public static String TOPIC_INTERFACE 	= "interface";
	public static String TOPIC_PACKAGE 	    = "package";
//	public static String TOPIC_FILE 		= "file";
	public static String TOPIC_SECTION 		= "section";
	public static String TOPIC_TASK 	    = "task";
	public static String TOPIC_FUNCTION 	= "function";
	public static String TOPIC_VARIABLE 	= "variable";
//	public static String TOPIC_PROPERTY 	= "property";
//	public static String TOPIC_TYPE 		= "type";
//	public static String TOPIC_CONSTANT 	= "constant";
//	public static String TOPIC_ENUMERATION 	= "enumeration";
//	public static String TOPIC_DELEGATE 	= "delegate";
//	public static String TOPIC_EVENT 		= "event";
	
	
	Map<String,DocTopicType>  topicTypeMap ;    	// topicTypeName -> TopicType
	Map<String,DocTopicType>  singularKeywordMap ;	// singular keyword -> TopicType
	Map<String,DocTopicType>  pluralKeywordMap ;	// plural keyword -> TopicType
	
	public DocTopicManager() {
		
		topicTypeMap 		= new HashMap<String,DocTopicType>() ;
		singularKeywordMap 	= new HashMap<String,DocTopicType>() ;
		pluralKeywordMap   	= new HashMap<String,DocTopicType>() ;
		
		//													name				plural			scope				index   pageTitleFirst		breakLists
		topicTypeMap.put(TOPIC_GENERAL,   	new DocTopicType(TOPIC_GENERAL,		"",				ScopeType.NORMAL, 	false,	true,				false)) ;
		topicTypeMap.put(TOPIC_CLASS,   	new DocTopicType(TOPIC_CLASS,		"classes",		ScopeType.START,	true,	true,				false)) ;
//		topicTypeMap.put(TOPIC_MODULE, 		new DocTopicType(TOPIC_MODULE,		"module",		ScopeType.START,	true,	false,				false)) ;
//		topicTypeMap.put(TOPIC_INTERFACE, 	new DocTopicType(TOPIC_INTERFACE,	"interface",	ScopeType.START,    true,	false,				false)) ;
		topicTypeMap.put(TOPIC_PACKAGE, 	new DocTopicType(TOPIC_PACKAGE,		"packages",		ScopeType.START,    true,	true,				false)) ;
		topicTypeMap.put(TOPIC_SECTION, 	new DocTopicType(TOPIC_SECTION,		"",				ScopeType.END,		false,	true,				false)) ;
		topicTypeMap.put(TOPIC_GROUP, 		new DocTopicType(TOPIC_GROUP,		"",				ScopeType.NORMAL,	false,	false,				false)) ;
		topicTypeMap.put(TOPIC_TASK, 		new DocTopicType(TOPIC_TASK,		"tasks",		ScopeType.NORMAL,	true,	false,				false)) ;
		topicTypeMap.put(TOPIC_FUNCTION, 	new DocTopicType(TOPIC_FUNCTION,	"functions",	ScopeType.NORMAL,   true,	false,				false)) ;
		topicTypeMap.put(TOPIC_VARIABLE, 	new DocTopicType(TOPIC_VARIABLE,	"variables",	ScopeType.NORMAL,   true,	false,				false)) ;
		
		registerKeywordForTopicType(TOPIC_GENERAL, 	"general", 	"") ;
		registerKeywordForTopicType(TOPIC_CLASS, 	"class", 	"classes") ;
		registerKeywordForTopicType(TOPIC_PACKAGE, 	"package", 	"packages") ;
		registerKeywordForTopicType(TOPIC_SECTION, 	"section", 	"") ;
		registerKeywordForTopicType(TOPIC_SECTION, 	"title", 	"") ;
		registerKeywordForTopicType(TOPIC_GROUP, 	"group", 	"") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "field", 	"fields") ;
		registerKeywordForTopicType(TOPIC_TASK, 	"task", 	"tasks") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "function", "functions") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "func", 	"funcs") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "variable", "variables") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "field", 	"fields") ;
		
	}

	private void registerKeywordForTopicType(String topicTypeName,
											 String singularKeyword, 
											 String pluralKeyword) {
		
		DocTopicType topicType = topicTypeMap.get(topicTypeName) ;
		
		if(topicType != null) {
			singularKeywordMap.put(singularKeyword, topicType) ;
			pluralKeywordMap.put(pluralKeyword, topicType) ;
		}
		
	}

	public DocKeywordInfo getTopicType(String keyword) {
		String kwLower = keyword.toLowerCase() ;
		if(singularKeywordMap.containsKey(kwLower))
			return new DocKeywordInfo(kwLower, singularKeywordMap.get(kwLower), false) ;
		if(pluralKeywordMap.containsKey(kwLower.toLowerCase())) 
			return new DocKeywordInfo(kwLower, pluralKeywordMap.get(kwLower), false) ;
		return null ;
	}

	public Collection<DocTopicType> getAllTopicTypes() {
		return new ArrayList<DocTopicType>(topicTypeMap.values()) ;
	}
	
	

}
