package net.sf.sveditor.ui.pref;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorTemplatePropertiesPrefsPage 
	extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVEditorTemplatePropertiesPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
//		setDescription("SystemVerilog Template Paths");
	}

	public void init(IWorkbench workbench) {
	}

	@Override
	protected void createFieldEditors() {
		TemplatePropertiesEditor ed = new TemplatePropertiesEditor(
				SVEditorPrefsConstants.P_SV_TEMPLATE_PROPERTIES, getFieldEditorParent());
		addField(ed);
	}
}
