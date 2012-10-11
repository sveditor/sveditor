package net.sf.sveditor.ui.argfile.editor;

import java.util.ResourceBundle;

import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.argfile.editor.actions.OpenDeclarationAction;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.TextEditor;

public class SVArgFileEditor extends TextEditor implements ILogLevel {
	private SVArgFileCodeScanner			fCodeScanner;
	
	public SVArgFileEditor() {
		fCodeScanner = new SVArgFileCodeScanner();
		
	}

	
	public SVArgFileCodeScanner getCodeScanner() {
		return fCodeScanner;
	}
	

	@Override
	protected void createActions() {
		super.createActions();
	
		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();

		OpenDeclarationAction od_action = new OpenDeclarationAction(bundle, this);
		od_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.declaration");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", od_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", false);
	}


	@Override
	protected void initializeKeyBindingScopes() {
		super.initializeKeyBindingScopes();
		setKeyBindingScopes(new String[] {SVUiPlugin.PLUGIN_ID + ".svArgFileEditorContext"});
	}


	@Override
	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new SVArgFileSourceViewerConfiguration(this));

		super.createPartControl(parent);
	}
	
	
	
}
