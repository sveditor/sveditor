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

import net.sf.sveditor.ui.SVUiPlugin;

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
		
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_DEFAULT_C, new RGB(0, 0, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_SL_COMMENT_C, new RGB(0, 128, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_ML_COMMENT_C, new RGB(0, 128, 0));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_STRING_C, new RGB(42, 0, 255));
		PreferenceConverter.setDefault(store, SVEditorPrefsConstants.P_KEYWORD_C, new RGB(128, 0, 64));

		store.setDefault(SVEditorPrefsConstants.P_DEFAULT_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_SL_COMMENT_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_ML_COMMENT_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_STRING_S, SWT.NORMAL);
		store.setDefault(SVEditorPrefsConstants.P_KEYWORD_S, SWT.BOLD);
		
		store.setDefault(SVEditorPrefsConstants.P_DEBUG_ENABLED_S, false);
		store.setDefault(SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S, true);
	}

}
