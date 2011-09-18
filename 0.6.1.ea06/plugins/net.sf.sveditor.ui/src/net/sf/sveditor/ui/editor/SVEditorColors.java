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


package net.sf.sveditor.ui.editor;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

public enum SVEditorColors {
	DEFAULT,
	KEYWORD,
	STRING,
	SINGLE_LINE_COMMENT,
	MULTI_LINE_COMMENT;

	private static Map<SVEditorColors, String>              fColorMap;
	private static Map<SVEditorColors, String>              fStyleMap;

	static {
		fColorMap = new HashMap<SVEditorColors, String>();
		fStyleMap = new HashMap<SVEditorColors, String>();

		
		fColorMap.put(DEFAULT, SVEditorPrefsConstants.P_DEFAULT_C);
		fColorMap.put(STRING, SVEditorPrefsConstants.P_STRING_C);
		fColorMap.put(SINGLE_LINE_COMMENT, SVEditorPrefsConstants.P_SL_COMMENT_C);
		fColorMap.put(MULTI_LINE_COMMENT, SVEditorPrefsConstants.P_ML_COMMENT_C);
		fColorMap.put(KEYWORD, SVEditorPrefsConstants.P_KEYWORD_C);
		
		fStyleMap.put(DEFAULT, SVEditorPrefsConstants.P_DEFAULT_S);
		fStyleMap.put(STRING, SVEditorPrefsConstants.P_STRING_S);
		fStyleMap.put(SINGLE_LINE_COMMENT, SVEditorPrefsConstants.P_SL_COMMENT_S);
		fStyleMap.put(MULTI_LINE_COMMENT, SVEditorPrefsConstants.P_ML_COMMENT_S);
		fStyleMap.put(KEYWORD, SVEditorPrefsConstants.P_KEYWORD_S);
	}

	static IPreferenceStore fPrefStore = SVUiPlugin.getDefault().getPreferenceStore();

	public static Color getColor(SVEditorColors color) {
		if (fColorMap.containsKey(color)) {
			return SVColorManager.getColor(PreferenceConverter.getColor(
					fPrefStore, fColorMap.get(color)));
		} else {
			return SVColorManager.getColor(PreferenceConverter.getColor(
					fPrefStore, fColorMap.get(DEFAULT)));
		}
	}
	
	public static int getStyle(SVEditorColors color) {
		if (fStyleMap.containsKey(color)) {
			return fPrefStore.getInt(fStyleMap.get(color));
		} else {
			return SWT.NORMAL;
		}
	}
}
