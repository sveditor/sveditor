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

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.XMLTransformUtils;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.templates.DefaultTemplateParameterProvider;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditorColors;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.RGB;

/**
 * Class used to initialize default preference values.
 */
public class SVEditorPrefsInitialize extends AbstractPreferenceInitializer {

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
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_NUMBERS_C, new RGB(0, 0, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_OPERATORS_C, new RGB(0, 0, 0));
		
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR, 
				new RGB(0xFF,0xFF,0xC0));
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
		
		store.setDefault(SVEditorPrefsConstants.P_DEBUG_LEVEL_S, "LEVEL_OFF");
		store.setDefault(SVEditorPrefsConstants.P_DEBUG_CONSOLE_S, false);
		store.setDefault(SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S, true);
		
		// Index Preferences
		store.setDefault(SVEditorPrefsConstants.P_AUTO_REBUILD_INDEX, true);
		store.setDefault(SVEditorPrefsConstants.P_ENABLE_SHADOW_INDEX, false);
		
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
		
		/**
		 * Initialize template parameters
		 */
		{
			Map<String, String> p = new HashMap<String, String>();
			p.put("file_header", DefaultTemplateParameterProvider.FILE_HEADER_DFLT);
			p.put("file_footer", DefaultTemplateParameterProvider.FILE_FOOTER_DFLT);
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
	}

}
