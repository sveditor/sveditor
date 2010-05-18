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


    public boolean performOk() {
    	boolean ok= super.performOk();

    	SVUiPlugin.getDefault().savePluginPreferences();

    	return ok;
    }


}
