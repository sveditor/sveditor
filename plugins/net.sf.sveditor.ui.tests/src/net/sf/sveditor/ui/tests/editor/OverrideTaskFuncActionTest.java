package net.sf.sveditor.ui.tests.editor;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.actions.OverrideTaskFuncAction;

public class OverrideTaskFuncActionTest extends OverrideTaskFuncAction {

	public OverrideTaskFuncActionTest(SVEditor editor) {
		super(SVUiPlugin.getDefault().getResources(), "OverrideTaskFunc.", editor);
	}
	
	
}
