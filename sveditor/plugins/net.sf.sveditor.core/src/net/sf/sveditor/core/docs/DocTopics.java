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

import java.util.HashMap;
import java.util.Map;

public class DocTopics implements IDocTopics {
	
//	public static String TOPIC_GENERAL 		= "general";
//	public static String TOPIC_GENERIC 		= "generic";
//	public static String TOPIC_GROUP 		= "group";
	public static String TOPIC_MODULE 		= "module";
	public static String TOPIC_CLASS 		= "class";
	public static String TOPIC_INTERFACE 	= "interface";
	public static String TOPIC_PACKAGE 	    = "package";
//	public static String TOPIC_FILE 		= "file";
//	public static String TOPIC_SECTION 		= "section";
	public static String TOPIC_TASK 	    = "task";
	public static String TOPIC_FUNCTION 	= "function";
//	public static String TOPIC_VARIABLE 	= "variable";
	public static String TOPIC_PROPERTY 	= "property";
//	public static String TOPIC_TYPE 		= "type";
//	public static String TOPIC_CONSTANT 	= "constant";
//	public static String TOPIC_ENUMERATION 	= "enumeration";
//	public static String TOPIC_DELEGATE 	= "delegate";
//	public static String TOPIC_EVENT 		= "event";
	
	
	Map<String,DocTopicType>  topicTypeMap ;    	// topicTypeName -> TopicType
	Map<String,DocTopicType>  singularKeywordMap ;	// singular keyword -> TopicType
	Map<String,DocTopicType>  pluralKeywordMap ;	// plural keyword -> TopicType
	
	public DocTopics() {
		
		topicTypeMap 		= new HashMap<String,DocTopicType>() ;
		singularKeywordMap 	= new HashMap<String,DocTopicType>() ;
		pluralKeywordMap   	= new HashMap<String,DocTopicType>() ;
		
		//													name				plural			index   pageTitleFirst		breakLists
		topicTypeMap.put(TOPIC_CLASS,   	new DocTopicType(TOPIC_CLASS,		"classes",		true,	false,				false)) ;
//		topicTypeMap.put(TOPIC_MODULE, 		new DocTopicType(TOPIC_MODULE,		"module",		true,	false,				false)) ;
//		topicTypeMap.put(TOPIC_INTERFACE, 	new DocTopicType(TOPIC_INTERFACE,	"interface",	true,	false,				false)) ;
//		topicTypeMap.put(TOPIC_PACKAGE, 	new DocTopicType(TOPIC_PACKAGE,		"packages",		true,	false,				false)) ;
		topicTypeMap.put(TOPIC_TASK, 		new DocTopicType(TOPIC_TASK,		"tasks",		true,	false,				false)) ;
		topicTypeMap.put(TOPIC_FUNCTION, 	new DocTopicType(TOPIC_FUNCTION,	"functions",	true,	false,				false)) ;
		topicTypeMap.put(TOPIC_PROPERTY, 	new DocTopicType(TOPIC_PROPERTY,	"properties",	true,	false,				false)) ;
		
		registerKeywordForTopicType(TOPIC_CLASS, 	"class", 	"classes") ;
		registerKeywordForTopicType(TOPIC_PACKAGE, 	"package", 	"packages") ;
		registerKeywordForTopicType(TOPIC_TASK, 	"task", 	"tasks") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "function", "functions") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "func", 	"funcs") ;
		
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
		if(singularKeywordMap.containsKey(keyword)) 
			return new DocKeywordInfo(keyword, singularKeywordMap.get(keyword), false) ;
		if(pluralKeywordMap.containsKey(keyword)) 
			return new DocKeywordInfo(keyword, pluralKeywordMap.get(keyword), false) ;
		return null ;
	}
	
	

}
