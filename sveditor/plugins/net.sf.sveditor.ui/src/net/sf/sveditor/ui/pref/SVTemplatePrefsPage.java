/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
