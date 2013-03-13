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
	
	private static final String EDIT_SETTINGS = "EditSettings.";
	private static final String OUTLINE_SETTINGS = "OutlineSettings.";
	private static final String TEMPLATE_SETTINGS = "TemplateSettings.";
	private static final String INDEX_SETTINGS = "IndexSettings.";
	
	public static final String P_DEFAULT_C 										= EDIT_SETTINGS + "defaultColorPreference";
	public static final String P_COMMENT_C 										= EDIT_SETTINGS + "singleLineCommentColorPreference";
	public static final String P_KEYWORD_C 										= EDIT_SETTINGS + "keywordColorPreference";
	public static final String P_STRING_C 										= EDIT_SETTINGS + "stringColorPreference";
	public static final String P_BRACE_C 										= EDIT_SETTINGS + "braceColorPreference";
	public static final String P_NUMBERS_C 										= EDIT_SETTINGS + "numbersColorPreference";
	public static final String P_OPERATORS_C									= EDIT_SETTINGS + "operatorsColorPreference";
	
	public static final String P_DEFAULT_S 										= EDIT_SETTINGS + "defaultStylePreference";
	public static final String P_KEYWORD_S 										= EDIT_SETTINGS + "keywordStylePreference";
	public static final String P_COMMENT_S 										= EDIT_SETTINGS + "singleLineCommentStylePreference";
	public static final String P_STRING_S 										= EDIT_SETTINGS + "stringStylePreference";
	public static final String P_BRACE_S 										= EDIT_SETTINGS + "braceStylePreference";
	public static final String P_NUMBERS_S										= EDIT_SETTINGS + "numbersStylePreference";
	public static final String P_OPERATORS_S									= EDIT_SETTINGS + "operatorsStylePreference";
	
	public static final String P_SV_FILE_EXTENSIONS_S 							= "svFileExtensions";
	
	public static final String P_AUTO_INDENT_ENABLED_S 							= EDIT_SETTINGS + "autoIndentEnabled";
	
	public static final String P_AUTO_REBUILD_INDEX								= "autoRebuildIndex";
	public static final String P_ENABLE_SHADOW_INDEX								= "enableShadowIndex";
	
	public static final String P_DEBUG_LEVEL_S 									= "debugLevel";
	public static final String P_DEBUG_CONSOLE_S 									= "debugConsole";
	
	public static final String P_CONTENT_ASSIST_TIMEOUT							= EDIT_SETTINGS + "contentAssistTimeout";
	
	public static final String P_CONTENT_ASSIST_TF_NAMED_PORTS_EN 				= EDIT_SETTINGS + "contentAssistTFNamedPortsEn";
	public static final String P_CONTENT_ASSIST_TF_LINE_WRAP_LIMIT 				= EDIT_SETTINGS + "contentAssistTFLineWrapLimit";
	public static final String P_CONTENT_ASSIST_TF_MAX_PARAMS_PER_LINE			= EDIT_SETTINGS + "contentAssistTFParamsPerLine";
	
	public static final String P_CONTENT_ASSIST_MODIFCINST_NAMED_PORTS_EN 		= EDIT_SETTINGS + "contentAssistModIfcInstNamedPortsEn";
	public static final String P_CONTENT_ASSIST_MODIFCINST_LINE_WRAP_LIMIT 		= EDIT_SETTINGS + "contentAssistModIfcInstLineWrapLimit";
	public static final String P_CONTENT_ASSIST_MODIFCINST_MAX_PORTS_PER_LINE 	= EDIT_SETTINGS + "contentAssistModIfcInstPortsPerLine";
	
	public static final String P_CONTENT_ASSIST_HOVER_USES_BROWSER				= EDIT_SETTINGS + "contentAssistHoverUsesBrowser";
	public static final String P_CONTENT_ASSIST_HOVER_BG_COLOR					= EDIT_SETTINGS + "contentAssistHoverBgColor";
	public static final String P_CONTENT_ASSIST_HOVER_FG_COLOR					= EDIT_SETTINGS + "contentAssistHoverFgColor";
	
	// SV Template Paths
	public static final String P_SV_TEMPLATE_PATHS								= TEMPLATE_SETTINGS + "svTemplatePaths";
	public static final String P_SV_TEMPLATE_PROPERTIES							= TEMPLATE_SETTINGS + "svTemplateProperties";

	// Outline view Preferences
	public static final String P_OUTLINE_SHOW_ALWAYS_BLOCKS                     	= OUTLINE_SETTINGS + "outlineShowAlwaysBlocks";
	public static final String P_OUTLINE_SHOW_ASSIGN_STATEMENTS                 	= OUTLINE_SETTINGS + "outlineShowAssignStatements";
	public static final String P_OUTLINE_SHOW_DEFINE_STATEMENTS                 	= OUTLINE_SETTINGS + "outlineShowDefineStatements";
	public static final String P_OUTLINE_SHOW_INITIAL_BLOCKS                    	= OUTLINE_SETTINGS + "outlineShowInitialBlocks";
	public static final String P_OUTLINE_SHOW_INCLUDE_FILES                     	= OUTLINE_SETTINGS + "outlineShowIncludeFiles";
	public static final String P_OUTLINE_SHOW_GENERATE_BLOCKS                   	= OUTLINE_SETTINGS + "outlineShowGenerateBlocks";
	public static final String P_OUTLINE_SHOW_MODULE_INSTANCES                  	= OUTLINE_SETTINGS + "outlineShowModuleInstances";
	public static final String P_OUTLINE_SHOW_SIGNAL_DECLARATIONS               	= OUTLINE_SETTINGS + "outlineShowSignalDeclarations";
	public static final String P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS        	= OUTLINE_SETTINGS + "outlineShowTaskFunctionDeclarations";
	public static final String P_OUTLINE_SHOW_ENUM_TYPEDEFS                     	= OUTLINE_SETTINGS + "outlineShowEnumTypedefs";
	public static final String P_OUTLINE_SHOW_ASSERTION_PROPERTIES              	= OUTLINE_SETTINGS + "outlineShowAssertionProperties";
	public static final String P_OUTLINE_SHOW_COVER_POINT_GROUP_CROSS           	= OUTLINE_SETTINGS + "outlineShowCoverPointGroupCross";
	public static final String P_OUTLINE_SHOW_CONSTRAINTS                       	= OUTLINE_SETTINGS + "outlineShowConstraints";
	public static final String P_OUTLINE_SORT                                   	= OUTLINE_SETTINGS + "outlineSort";

	// Code Style Preferences
	public static final String P_SV_CODE_STYLE_PREFS								= INDEX_SETTINGS + "codeStylePrefs";
}
