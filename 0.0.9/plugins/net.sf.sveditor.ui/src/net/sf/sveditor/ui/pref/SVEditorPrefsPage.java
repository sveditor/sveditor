package net.sf.sveditor.ui.pref;
import org.eclipse.jface.preference.*;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.IWorkbench;
import net.sf.sveditor.ui.SVUiPlugin;

public class SVEditorPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public SVEditorPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Syntax Coloring");
	}

	public void createFieldEditors() {
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_DEFAULT_C, "Default test color:", SVEditorPrefsConstants.P_DEFAULT_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_SL_COMMENT_C, "Comment color:", SVEditorPrefsConstants.P_SL_COMMENT_S, getFieldEditorParent()));
		//FIXME: multi line comments are not identified by scanner, once support for milti line added uncomment lines below, and comment one above
//		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_SL_COMMENT_C, "Single line comment color:", SVEditorPrefsConstants.P_SL_COMMENT_S, getFieldEditorParent()));
//		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_ML_COMMENT_C, "Multi line comment color:", SVEditorPrefsConstants.P_ML_COMMENT_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_STRING_C, "String color:", SVEditorPrefsConstants.P_STRING_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_KEYWORD_C, "Keyword color:", SVEditorPrefsConstants.P_KEYWORD_S, getFieldEditorParent()));
		
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_DEBUG_ENABLED_S, "Enable Debug:", getFieldEditorParent()));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
}
