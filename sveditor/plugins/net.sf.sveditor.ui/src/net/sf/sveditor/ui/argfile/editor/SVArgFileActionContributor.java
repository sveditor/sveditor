package net.sf.sveditor.ui.argfile.editor;

import java.util.ResourceBundle;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.editors.text.TextEditorActionContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;

public class SVArgFileActionContributor extends TextEditorActionContributor {
	protected RetargetTextEditorAction fOpenDeclarationAction;

	
	public SVArgFileActionContributor() {
		super();
		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();
		
		fOpenDeclarationAction = new RetargetTextEditorAction(
				bundle, "OpenDeclaration.");
		fOpenDeclarationAction.setActionDefinitionId(
				"net.sf.sveditor.ui.editor.open.declaration");		
	}
	
	public void contributeToMenu(IMenuManager mm) {
		super.contributeToMenu(mm);
	
		/*
		IMenuManager editMenu = 
				mm.findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);
		if (editMenu != null) {
			editMenu.add(new Separator());
			editMenu.add(fOpenDeclarationAction);
		}
		 */
	}
	
	public void init(IActionBars bars) {
		super.init(bars);
	
		/*
		IMenuManager menuManager = bars.getMenuManager();
		IMenuManager editMenu = menuManager.findMenuUsingPath(
				IWorkbenchActionConstants.M_EDIT);
		
		if (editMenu != null) {
			editMenu.add(new Separator());
			editMenu.add(fOpenDeclarationAction);
		}
		 */
	}

	private void doSetActiveEditor(IEditorPart part) {
		super.setActiveEditor(part);

		/*
		ITextEditor editor= null;
		if (part instanceof ITextEditor)
			editor= (ITextEditor) part;

		fOpenDeclarationAction.setAction(getAction(editor, "OpenDeclaration"));
		 */
	}

	public void setActiveEditor(IEditorPart part) {
		super.setActiveEditor(part);
		doSetActiveEditor(part);
	}

	/*
	 * @see IEditorActionBarContributor#dispose()
	 */
	public void dispose() {
		doSetActiveEditor(null);
		super.dispose();
	}
}
