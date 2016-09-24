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
	public static String TOPIC_MACRO		= "macro";
	public static String TOPIC_MODULE 		= "module";
	public static String TOPIC_CLASS 		= "class";
	public static String TOPIC_PROGRAM 		= "program";
	public static String TOPIC_CONSTRAINT	= "constraint";
	public static String TOPIC_COVERGROUP	= "covergroup";
	public static String TOPIC_COVERPOINT	= "coverpoint";
	public static String TOPIC_INTERFACE 	= "interface";
	public static String TOPIC_MODPORT 		= "modport";
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
	
	
	public static final Map<String,DocTopicType>  topicTypeMap ;    	// topicTypeName -> TopicType
	public static final Map<String,DocTopicType>  singularKeywordMap ;	// singular keyword -> TopicType
	public static final Map<String,DocTopicType>  pluralKeywordMap ;	// plural keyword -> TopicType
	
	static {
		topicTypeMap 		= new HashMap<String,DocTopicType>() ;
		singularKeywordMap 	= new HashMap<String,DocTopicType>() ;
		pluralKeywordMap   	= new HashMap<String,DocTopicType>() ;
		
		//													name				plural			scope				index   pageTitleFirst		breakLists
		topicTypeMap.put(TOPIC_GENERAL,   	new DocTopicType(TOPIC_GENERAL,		"",				ScopeType.NORMAL, 	false,	true,				false)) ;
		topicTypeMap.put(TOPIC_CLASS,   	new DocTopicType(TOPIC_CLASS,		"classes",		ScopeType.START,	true,	true,				false)) ;
		topicTypeMap.put(TOPIC_CONSTRAINT, 	new DocTopicType(TOPIC_CONSTRAINT,	"constraints",	ScopeType.NORMAL,	true,	false,				false)) ;
		topicTypeMap.put(TOPIC_COVERGROUP, 	new DocTopicType(TOPIC_COVERGROUP,	"covergroups",	ScopeType.NORMAL,	true,	false,				false)) ;
		topicTypeMap.put(TOPIC_COVERPOINT, 	new DocTopicType(TOPIC_COVERPOINT,	"coverpoints",	ScopeType.NORMAL,	true,	false,				false)) ;
		topicTypeMap.put(TOPIC_MODULE, 		new DocTopicType(TOPIC_MODULE,		"module",		ScopeType.START,	true,	true,				false)) ;
		topicTypeMap.put(TOPIC_INTERFACE, 	new DocTopicType(TOPIC_INTERFACE,	"interface",	ScopeType.START,    true,	true,				false)) ;
		topicTypeMap.put(TOPIC_PACKAGE, 	new DocTopicType(TOPIC_PACKAGE,		"packages",		ScopeType.START,    true,	true,				false)) ;
		topicTypeMap.put(TOPIC_SECTION, 	new DocTopicType(TOPIC_SECTION,		"",				ScopeType.END,		false,	true,				false)) ;
		topicTypeMap.put(TOPIC_GROUP, 		new DocTopicType(TOPIC_GROUP,		"",				ScopeType.NORMAL,	false,	false,				false)) ;
		topicTypeMap.put(TOPIC_TASK, 		new DocTopicType(TOPIC_TASK,		"tasks",		ScopeType.NORMAL,	true,	false,				false)) ;
		topicTypeMap.put(TOPIC_FUNCTION, 	new DocTopicType(TOPIC_FUNCTION,	"functions",	ScopeType.NORMAL,   true,	false,				false)) ;
		topicTypeMap.put(TOPIC_VARIABLE, 	new DocTopicType(TOPIC_VARIABLE,	"variables",	ScopeType.NORMAL,   true,	false,				false)) ;
		topicTypeMap.put(TOPIC_MACRO, 		new DocTopicType(TOPIC_MACRO,		"macros",		ScopeType.START,   	true,	true,				false)) ;
		
		registerKeywordForTopicType(TOPIC_GENERAL, 	"general", 		"") ;
		
		registerKeywordForTopicType(TOPIC_CLASS, 	"class", 		"classes") ;
		registerKeywordForTopicType(TOPIC_CLASS, 	"struct", 		"structs") ;
		registerKeywordForTopicType(TOPIC_CLASS, 	"structure", 	"structures") ;
		
		registerKeywordForTopicType(TOPIC_MACRO, 	"macro", 		"macros");
		
		registerKeywordForTopicType(TOPIC_CONSTRAINT, 	"constraint", 		"constraints") ;
		
		registerKeywordForTopicType(TOPIC_COVERGROUP, 	"covergroup", 		"covergroups") ;
		registerKeywordForTopicType(TOPIC_COVERPOINT, 	"coverpoint", 		"coverpoints") ;
		
		registerKeywordForTopicType(TOPIC_PACKAGE, 	"package", 		"packages") ;
		
		registerKeywordForTopicType(TOPIC_MODULE, 	"module", 		"modules") ;
		registerKeywordForTopicType(TOPIC_INTERFACE,"interface", 	"interfaces") ;
		
		registerKeywordForTopicType(TOPIC_SECTION, 	"section", 		"") ;
		registerKeywordForTopicType(TOPIC_SECTION, 	"title", 		"") ;
		
		registerKeywordForTopicType(TOPIC_GROUP, 	"group", 		"") ;
		
		registerKeywordForTopicType(TOPIC_VARIABLE, "field", 		"fields") ;
		
		registerKeywordForTopicType(TOPIC_TASK, 	"task", 		"tasks") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "function", 	"functions") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "func", 		"funcs") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "method",   	"methods") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "meth", 		"meths") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "procedure",	"procedures") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "proc", 		"procs") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "routine",  	"routines") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "callback",  	"callbacks") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "constructor",  "constructors") ;
		registerKeywordForTopicType(TOPIC_FUNCTION, "destructor",  	"destructors") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "variable", 	"variables") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "var", 			"vars") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "integer", 		"integers") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "uint", 		"uints") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "byte", 		"bytes") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "scalar", 		"scalars") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "array", 		"arrays") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "boolean", 		"booleans") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "bool", 		"bools") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "flag", 		"flags") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "bit", 			"bits") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "bitfield", 	"bitfields") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "field", 		"fields") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "pointer", 		"pointers") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "ptr", 			"ptrs") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "reference", 	"references") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "ref", 			"refs") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "object", 		"objects") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "character", 	"characters") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "string", 		"strings") ;
		registerKeywordForTopicType(TOPIC_VARIABLE, "handle", 		"handles") ;		
	}
	
	public DocTopicManager() {
		

		
	}

	private static void registerKeywordForTopicType(String topicTypeName,
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
