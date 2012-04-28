/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.pref;

public class SVEditorPrefsConstants {
	
	public static final String P_DEFAULT_C = "defaultColorPreference";
	public static final String P_COMMENT_C = "singleLineCommentColorPreference";
	public static final String P_KEYWORD_C = "keywordColorPreference";
	public static final String P_STRING_C = "stringColorPreference";
	
	public static final String P_DEFAULT_S = "defaultStylePreference";
	public static final String P_KEYWORD_S = "keywordStylePreference";
	public static final String P_COMMENT_S = "singleLineCommentStylePreference";
	public static final String P_STRING_S = "stringStylePreference";
	
	public static final String P_SV_FILE_EXTENSIONS_S 							= "svFileExtensions";
	
	public static final String P_AUTO_INDENT_ENABLED_S 							= "autoIndentEnabled";
	
	public static final String P_AUTO_REBUILD_INDEX								= "autoRebuildIndex";
	
	public static final String P_DEBUG_LEVEL_S 									= "debugLevel";
	
	public static final String P_CONTENT_ASSIST_TF_NAMED_PORTS_EN 				= "contentAssistTFNamedPortsEn";
	public static final String P_CONTENT_ASSIST_TF_LINE_WRAP_LIMIT 				= "contentAssistTFLineWrapLimit";
	public static final String P_CONTENT_ASSIST_TF_MAX_PARAMS_PER_LINE			= "contentAssistTFParamsPerLine";
	
	public static final String P_CONTENT_ASSIST_MODIFCINST_NAMED_PORTS_EN 		= "contentAssistModIfcInstNamedPortsEn";
	public static final String P_CONTENT_ASSIST_MODIFCINST_LINE_WRAP_LIMIT 		= "contentAssistModIfcInstLineWrapLimit";
	public static final String P_CONTENT_ASSIST_MODIFCINST_MAX_PORTS_PER_LINE 	= "contentAssistModIfcInstPortsPerLine";
	
	
	// SV Template Paths
	public static final String P_SV_TEMPLATE_PATHS								= "svTemplatePaths";

	// Outline view Preferences
	public static final String P_OUTLINE_SHOW_ALWAYS_BLOCKS                     	= "outlineShowAlwaysBlocks";
	public static final String P_OUTLINE_SHOW_ASSIGN_STATEMENTS                 	= "outlineShowAssignStatements";
	public static final String P_OUTLINE_SHOW_DEFINE_STATEMENTS                 	= "outlineShowDefineStatements";
	public static final String P_OUTLINE_SHOW_INITIAL_BLOCKS                    	= "outlineShowInitialBlocks";
	public static final String P_OUTLINE_SHOW_INCLUDE_FILES                     	= "outlineShowIncludeFiles";
	public static final String P_OUTLINE_SHOW_GENERATE_BLOCKS                   	= "outlineShowGenerateBlocks";
	public static final String P_OUTLINE_SHOW_MODULE_INSTANCES                  	= "outlineShowModuleInstances";
	public static final String P_OUTLINE_SHOW_SIGNAL_DECLARATIONS               	= "outlineShowSignalDeclarations";
	public static final String P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS        	= "outlineShowTaskFunctionDeclarations";
	public static final String P_OUTLINE_SORT                                   	= "outlineSort";
	
}
