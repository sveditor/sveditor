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

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.ui.texteditor.templates.TemplatePreferencePage;



public class SVTemplatePrefsPage extends TemplatePreferencePage {
	
	public SVTemplatePrefsPage() {
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setTemplateStore(SVUiPlugin.getDefault().getTemplateStore());
		setContextTypeRegistry(SVUiPlugin.getDefault().getContextTypeRegistry());
	}
	
    protected boolean isShowFormatterSetting() {
        return false;
    }


    @SuppressWarnings("deprecation")
    public boolean performOk() {
    	boolean ok= super.performOk();

    	SVUiPlugin.getDefault().savePluginPreferences();

    	return ok;
    }


}
