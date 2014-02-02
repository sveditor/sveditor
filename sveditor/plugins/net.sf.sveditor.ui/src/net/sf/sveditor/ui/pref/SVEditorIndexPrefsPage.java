package net.sf.sveditor.ui.pref;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorIndexPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVEditorIndexPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Index Preferences");
	}

	public void init(IWorkbench workbench) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void createFieldEditors() {
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_AUTO_REBUILD_INDEX, 
				"Enable Index Auto-Rebuild:", getFieldEditorParent()));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_ENABLE_SHADOW_INDEX, 
				"Enable Shadow Index:", getFieldEditorParent()));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_ENABLE_SHADOW_INDEX, 
				"Override Language Level based on file extension. Treat all source as SystemVerilog:", 
				getFieldEditorParent()));
		
		IntegerFieldEditor fi = new IntegerFieldEditor(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY, 
				"Editor Auto-Index Delay (mS):", getFieldEditorParent());
		fi.setValidRange(-1, Integer.MAX_VALUE);
		addField(fi);
		
	}

}
