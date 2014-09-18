package net.sf.sveditor.vhdl.ui.tests;

import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.tests.utils.editor.EditorTestCaseBase;
import net.sf.sveditor.vhdl.ui.editor.VHDLEditor;

import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;

public class VhdlEditorTestCaseBase extends EditorTestCaseBase {

	protected VHDLEditor openEditor(String path) throws PartInitException {
		IEditorPart ed = SVEditorUtil.openEditor(path);
		assertNotNull(ed);
		assertTrue((ed instanceof VHDLEditor));
		
		while (Display.getDefault().readAndDispatch()) {}
	
		VHDLEditor sv_ed = (VHDLEditor)ed;
		addEditor(sv_ed);
		
		return sv_ed;
	}
}
