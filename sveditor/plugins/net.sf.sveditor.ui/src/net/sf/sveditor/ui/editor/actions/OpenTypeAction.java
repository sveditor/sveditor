package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.dialog.types.SVOpenTypeDialog;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenTypeAction extends TextEditorAction {
	private SVEditor				fEditor;
	
	public OpenTypeAction(
			ResourceBundle		bundle,
			SVEditor			editor) {
		super(bundle, "OpenType.", editor);
		fEditor = editor;
	}

	@Override
	public void run() {
		Shell shell = fEditor.getSite().getWorkbenchWindow().getShell();
		
		SVOpenTypeDialog dlg = new SVOpenTypeDialog(fEditor.getIndexIterator(), shell);
		
		if (dlg.open() == Window.OK) {
			Object sel = dlg.getFirstResult();
			if (sel instanceof SVDBDeclCacheItem) {
				SVDBDeclCacheItem ci = (SVDBDeclCacheItem)sel;
				ISVDBItemBase item = ci.getSVDBItem();
				try {
					SVEditorUtil.openEditor(item);
				} catch (PartInitException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
}
