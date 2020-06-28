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


package net.sf.sveditor.ui.pref;

import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.text.spelling.PreferenceConstants;
import net.sf.sveditor.ui.text.spelling.SpellCheckEngine;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.hdt.sveditor.core.XMLTransformUtils;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.RGB;

/**
 * Class used to initialize default preference values.
 */
public class SVEditorPrefsInitialize extends AbstractPreferenceInitializer {
	public static final String				FILE_HEADER = "file_header";
	public static final String				FILE_HEADER_DFLT =
			"/****************************************************************************\n" +
			" * ${filename}\n" +
			" ****************************************************************************/\n";

	public static final String				FILE_FOOTER = "file_footer";
	public static final String				FILE_FOOTER_DFLT = "";	

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
	 */
	public void initializeDefaultPreferences() {
		IPreferenceStore store = SVUiPlugin.getDefault().getPreferenceStore();
		
		// Colorizer colors
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_DEFAULT_C, new RGB(0, 0, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_COMMENT_C, new RGB(0, 128, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_STRING_C, new RGB(42, 0, 255));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_KEYWORD_C, new RGB(128, 0, 64));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_BRACE_C  , new RGB(0, 0, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_MATCHING_BRACE_C, new RGB(170, 170, 170));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_NUMBERS_C, new RGB(0, 0, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_OPERATORS_C, new RGB(0, 0, 0));
		
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR, 
				new RGB(0xFF,0xFF,0xE1));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR, 
				new RGB(0x00,0x00,0x00));

		// Colorizer styles
		store.setDefault(SVEditorPrefsConstants.P_DEFAULT_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_COMMENT_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_STRING_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_KEYWORD_S, SWT.BOLD);
		store.setDefault(SVEditorPrefsConstants.P_BRACE_S  , SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_NUMBERS_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_OPERATORS_S, SWT.NORMAL);
		PreferenceConverter.setDefault(store,  SVEditorPrefsConstants.P_SVT_PARAMETERS_S, 
				new RGB(225, 20, 225));
		
		store.setDefault(SVEditorPrefsConstants.P_DEBUG_LEVEL_S, "LEVEL_OFF");
		store.setDefault(SVEditorPrefsConstants.P_DEBUG_CONSOLE_S, false);
		store.setDefault(SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S, true);
		
		// Index Preferences
		store.setDefault(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_ENABLE, true);
		store.setDefault(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY, 0);
		
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_TIMEOUT, 0);
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_USES_BROWSER, false);
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_NAMED_PORTS_EN, false);
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_LINE_WRAP_LIMIT, 80);
		// 0 means don't bother splitting the parameters across lines
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_MAX_PARAMS_PER_LINE, 0);
		
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_NAMED_PORTS_EN, true);
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_LINE_WRAP_LIMIT, 80);
		// 0 means don't bother splitting the parameters across lines
		store.setDefault(SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_MAX_PORTS_PER_LINE, 1);
		
		store.setDefault(SVEditorPrefsConstants.P_OUTLINE_LINK_WITH_EDITOR, true);
		
		// Initialize folding parameters
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_ENABLE, true);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_MODULES, false);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_INTERFACES, false);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_CLASSES, false);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_TF, false);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_UNPROCESSED, true);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_HEADER_COMMENTS, true);
		store.setDefault(SVEditorPrefsConstants.P_FOLDING_INIT_BLOCK_COMMENTS, false);

		// Save Actions
		store.setDefault(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE, false);
		store.setDefault(SVEditorPrefsConstants.P_REMOVE_TRAILING_WHITESPACE, false);
		store.setDefault(SVEditorPrefsConstants.P_NEWLINE_AT_END_OF_FILE, false);
		store.setDefault(SVEditorPrefsConstants.P_FORMAT_SOURCE_CODE, false);
		
		/**
		 * Initialize template parameters
		 */
		{
			// TODO: this isn't exactly the way we want this partitioned
			Map<String, String> p = new HashMap<String, String>();
			p.put("file_header", FILE_HEADER_DFLT);
			p.put("file_footer", FILE_FOOTER_DFLT);
			try {
				store.setDefault(SVEditorPrefsConstants.P_SV_TEMPLATE_PROPERTIES,
						XMLTransformUtils.map2Xml(p, "parameters", "parameter"));
			} catch (Exception e) {}
		}
		
		/**
		 * Initialize code-style preferences
		 */
		{
			Map<String, String> map = new HashMap<String, String>();
			for (String key : SVParserConfig.getOptionSet()) {
				map.put(key, "false");
			}
			try {
				String val = XMLTransformUtils.map2Xml(map, "preferences", "preference");
				store.setDefault(SVEditorPrefsConstants.P_SV_CODE_STYLE_PREFS, val);
			} catch (Exception e) {}
		}
		
		/**
		 * Initialize spelling preferences
		 */
		{
			store.setDefault(PreferenceConstants.SPELLING_LOCALE, "en_US"); //$NON-NLS-1$
			String isInitializedKey= "spelling_locale_initialized"; //$NON-NLS-1$
			if (!store.getBoolean(isInitializedKey)) {
				store.setValue(isInitializedKey, true);
				Locale locale= SpellCheckEngine.getDefaultLocale();
				locale= SpellCheckEngine.findClosestLocale(locale);
				if (locale != null)
					store.setValue(PreferenceConstants.SPELLING_LOCALE, locale.toString());
			}
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_DIGITS, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_MIXED, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_SENTENCE, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_UPPER, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_URLS, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_SINGLE_LETTERS, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_AMPERSAND_IN_PROPERTIES, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_NON_LETTERS, true);
			store.setDefault(PreferenceConstants.SPELLING_IGNORE_JAVA_STRINGS, true);
			store.setDefault(PreferenceConstants.SPELLING_USER_DICTIONARY, ""); //$NON-NLS-1$

			// Note: For backwards compatibility we must use the property and not the workspace default
			store.setDefault(PreferenceConstants.SPELLING_USER_DICTIONARY_ENCODING, System.getProperty("file.encoding")); //$NON-NLS-1$

			store.setDefault(PreferenceConstants.SPELLING_PROPOSAL_THRESHOLD, 20);
			store.setDefault(PreferenceConstants.SPELLING_PROBLEMS_THRESHOLD, 100);			
		}
	}

}
