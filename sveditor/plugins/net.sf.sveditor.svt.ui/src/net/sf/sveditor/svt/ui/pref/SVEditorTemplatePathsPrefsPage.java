package net.sf.sveditor.svt.ui.pref;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorTemplatePathsPrefsPage 
	extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVEditorTemplatePathsPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
//		setDescription("SystemVerilog Template Paths");
	}

	public void init(IWorkbench workbench) {
	}

	@Override
	protected void createFieldEditors() {
		addField(new TemplatePathsEditor(SVEditorPrefsConstants.P_SV_TEMPLATE_PATHS, getFieldEditorParent()));
	}
}
