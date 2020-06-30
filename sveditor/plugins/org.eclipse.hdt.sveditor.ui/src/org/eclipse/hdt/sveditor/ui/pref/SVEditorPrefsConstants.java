/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui.pref;

import java.util.HashSet;
import java.util.Set;

public class SVEditorPrefsConstants {
	
	private static final String EDIT_SETTINGS = "EditSettings.";
	private static final String OUTLINE_SETTINGS = "OutlineSettings.";
	private static final String TEMPLATE_SETTINGS = "TemplateSettings.";
	private static final String INDEX_SETTINGS = "IndexSettings.";
	private static final String SAVE_ACTIONS_SETTINGS = "SaveActionsSettings.";
	private static final String FOLDING_SETTINGS = EDIT_SETTINGS + "Folding";
	
	public static final String P_DEFAULT_C 										= EDIT_SETTINGS + "defaultColorPreference";
	public static final String P_COMMENT_C 										= EDIT_SETTINGS + "singleLineCommentColorPreference";
	public static final String P_KEYWORD_C 										= EDIT_SETTINGS + "keywordColorPreference";
	public static final String P_STRING_C 										= EDIT_SETTINGS + "stringColorPreference";
	public static final String P_BRACE_C 										= EDIT_SETTINGS + "braceColorPreference";
	public static final String P_MATCHING_BRACE_C								= EDIT_SETTINGS + "matchingBraceColorPreference";
	public static final String P_NUMBERS_C 										= EDIT_SETTINGS + "numbersColorPreference";
	public static final String P_OPERATORS_C									= EDIT_SETTINGS + "operatorsColorPreference";
	
	public static final String P_DEFAULT_S 										= EDIT_SETTINGS + "defaultStylePreference";
	public static final String P_KEYWORD_S 										= EDIT_SETTINGS + "keywordStylePreference";
	public static final String P_COMMENT_S 										= EDIT_SETTINGS + "singleLineCommentStylePreference";
	public static final String P_STRING_S 										= EDIT_SETTINGS + "stringStylePreference";
	public static final String P_BRACE_S 										= EDIT_SETTINGS + "braceStylePreference";
	public static final String P_NUMBERS_S										= EDIT_SETTINGS + "numbersStylePreference";
	public static final String P_OPERATORS_S									= EDIT_SETTINGS + "operatorsStylePreference";
	
	public static final String P_SVT_PARAMETERS_S								= EDIT_SETTINGS + "svtParametersStylePreference";
	
	public static final String P_SV_FILE_EXTENSIONS_S 							= "svFileExtensions";
	
	public static final String P_AUTO_INDENT_ENABLED_S 							= EDIT_SETTINGS + "autoIndentEnabled";
	
	public static final String P_OVERRIDE_FILE_EXTENSION_LANGUAGE_LEVEL			= "overrideFileExtensionLanguageLevel";
	
	public static final String P_EDITOR_AUTOINDEX_ENABLE						= EDIT_SETTINGS + "autoIndexEnable";
	public static final String P_EDITOR_AUTOINDEX_DELAY							= EDIT_SETTINGS + "autoIndexDelay";
	
	public static final String P_DEBUG_LEVEL_S 									= "debugLevel";
	public static final String P_DEBUG_CONSOLE_S 								= "debugConsole";
	
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

	// Folding Settings
	public static final String P_FOLDING_ENABLE									= FOLDING_SETTINGS + "enableFolding";
	public static final String P_FOLDING_INIT_MODULES							= FOLDING_SETTINGS + "initFoldModules";
	public static final String P_FOLDING_INIT_INTERFACES						= FOLDING_SETTINGS + "initFoldInterfaces";
	public static final String P_FOLDING_INIT_CLASSES							= FOLDING_SETTINGS + "initFoldClasses";
	public static final String P_FOLDING_INIT_TF								= FOLDING_SETTINGS + "initFoldTasksFunctions";
	public static final String P_FOLDING_INIT_UNPROCESSED						= FOLDING_SETTINGS + "initFoldUnprocessed";
	public static final String P_FOLDING_INIT_HEADER_COMMENTS					= FOLDING_SETTINGS + "initFoldHeaderComments";
	public static final String P_FOLDING_INIT_BLOCK_COMMENTS					= FOLDING_SETTINGS + "initFoldBlockComments";
	
	public static final Set<String> P_FOLDING_PREFS;
	
	static {
		P_FOLDING_PREFS = new HashSet<String>();
		P_FOLDING_PREFS.add(P_FOLDING_ENABLE);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_CLASSES);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_MODULES);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_INTERFACES);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_UNPROCESSED);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_TF);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_HEADER_COMMENTS);
		P_FOLDING_PREFS.add(P_FOLDING_INIT_BLOCK_COMMENTS);
	};
	
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
	public static final String P_OUTLINE_LINK_WITH_EDITOR               			= OUTLINE_SETTINGS + "linkWithEditor";

	// Code Style Preferences
	public static final String P_SV_CODE_STYLE_PREFS								= INDEX_SETTINGS + "codeStylePrefs";
	
	// Save Actions Preferences
	public static final String P_PERFORM_ACTIONS_ON_SAVE							= SAVE_ACTIONS_SETTINGS + "performActionsOnSave";
	public static final String P_REMOVE_TRAILING_WHITESPACE							= SAVE_ACTIONS_SETTINGS + "removeTrailingWhitespace";
	public static final String P_NEWLINE_AT_END_OF_FILE								= SAVE_ACTIONS_SETTINGS + "ensureNewlineAtEndOfFile";
	public static final String P_FORMAT_SOURCE_CODE									= SAVE_ACTIONS_SETTINGS + "FormatSourceCode";
	
}
