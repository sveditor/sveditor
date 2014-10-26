package net.sf.sveditor.ui.pref;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorFoldingPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVEditorFoldingPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Folding");
	}

	public void init(IWorkbench workbench) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void createFieldEditors() {
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_ENABLE, 
				"Enable folding when opening a new editor", getFieldEditorParent()));
		
		Group g = new Group(getFieldEditorParent(), SWT.NONE);
		g.setText("Initially fold these regions");
		
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_CLASSES, 
				"Classes", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_INTERFACES, 
				"Interfaces", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_MODULES, 
				"Modules", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_TF, 
				"Tasks/Functions", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_UNPROCESSED, 
				"Unprocessed Regions", g));
		
	}

}
